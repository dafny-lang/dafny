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
    BigInteger dtor_dims { get; }
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
    public BigInteger dtor_dims {
      get {
        var d = this;
        return ((Type_Array)d)._dims;
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
    public readonly BigInteger _dims;
    public Type_Array(DAST._IType element, BigInteger dims) : base() {
      this._element = element;
      this._dims = dims;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Array(_element, _dims);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Array;
      return oth != null && object.Equals(this._element, oth._element) && this._dims == oth._dims;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._element));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._dims));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Array";
      s += "(";
      s += Dafny.Helpers.ToString(this._element);
      s += ", ";
      s += Dafny.Helpers.ToString(this._dims);
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
    DAST._IOptional<DAST._IExpression> dtor_maybeValue { get; }
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
    public static _IStatement create_Labeled(Dafny.ISequence<Dafny.Rune> lbl, Dafny.ISequence<DAST._IStatement> body) {
      return new Statement_Labeled(lbl, body);
    }
    public static _IStatement create_While(DAST._IExpression cond, Dafny.ISequence<DAST._IStatement> body) {
      return new Statement_While(cond, body);
    }
    public static _IStatement create_Foreach(Dafny.ISequence<Dafny.Rune> boundName, DAST._IType boundType, DAST._IExpression over, Dafny.ISequence<DAST._IStatement> body) {
      return new Statement_Foreach(boundName, boundType, over, body);
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
    public Dafny.ISequence<Dafny.Rune> dtor_lbl {
      get {
        var d = this;
        return ((Statement_Labeled)d)._lbl;
      }
    }
    public Dafny.ISequence<DAST._IStatement> dtor_body {
      get {
        var d = this;
        if (d is Statement_Labeled) { return ((Statement_Labeled)d)._body; }
        if (d is Statement_While) { return ((Statement_While)d)._body; }
        if (d is Statement_Foreach) { return ((Statement_Foreach)d)._body; }
        return ((Statement_TailRecursive)d)._body;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_boundName {
      get {
        var d = this;
        return ((Statement_Foreach)d)._boundName;
      }
    }
    public DAST._IType dtor_boundType {
      get {
        var d = this;
        return ((Statement_Foreach)d)._boundType;
      }
    }
    public DAST._IExpression dtor_over {
      get {
        var d = this;
        return ((Statement_Foreach)d)._over;
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
  public class Statement_Labeled : Statement {
    public readonly Dafny.ISequence<Dafny.Rune> _lbl;
    public readonly Dafny.ISequence<DAST._IStatement> _body;
    public Statement_Labeled(Dafny.ISequence<Dafny.Rune> lbl, Dafny.ISequence<DAST._IStatement> body) : base() {
      this._lbl = lbl;
      this._body = body;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_Labeled(_lbl, _body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_Labeled;
      return oth != null && object.Equals(this._lbl, oth._lbl) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._lbl));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Labeled";
      s += "(";
      s += this._lbl.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
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
      hash = ((hash << 5) + hash) + 4;
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
  public class Statement_Foreach : Statement {
    public readonly Dafny.ISequence<Dafny.Rune> _boundName;
    public readonly DAST._IType _boundType;
    public readonly DAST._IExpression _over;
    public readonly Dafny.ISequence<DAST._IStatement> _body;
    public Statement_Foreach(Dafny.ISequence<Dafny.Rune> boundName, DAST._IType boundType, DAST._IExpression over, Dafny.ISequence<DAST._IStatement> body) : base() {
      this._boundName = boundName;
      this._boundType = boundType;
      this._over = over;
      this._body = body;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_Foreach(_boundName, _boundType, _over, _body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_Foreach;
      return oth != null && object.Equals(this._boundName, oth._boundName) && object.Equals(this._boundType, oth._boundType) && object.Equals(this._over, oth._over) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._boundName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._boundType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._over));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Foreach";
      s += "(";
      s += this._boundName.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._boundType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._over);
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
      hash = ((hash << 5) + hash) + 6;
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
      hash = ((hash << 5) + hash) + 7;
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
      hash = ((hash << 5) + hash) + 8;
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
      hash = ((hash << 5) + hash) + 9;
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
      hash = ((hash << 5) + hash) + 10;
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
      hash = ((hash << 5) + hash) + 11;
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
      hash = ((hash << 5) + hash) + 12;
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
      hash = ((hash << 5) + hash) + 13;
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
    bool is_SeqConstruct { get; }
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
    bool is_BoolBoundedPool { get; }
    bool is_IntRange { get; }
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
    DAST._IExpression dtor_length { get; }
    DAST._IExpression dtor_elem { get; }
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
    BigInteger dtor_dim { get; }
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
    public static _IExpression create_SeqConstruct(DAST._IExpression length, DAST._IExpression elem) {
      return new Expression_SeqConstruct(length, elem);
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
    public static _IExpression create_ArrayLen(DAST._IExpression expr, BigInteger dim) {
      return new Expression_ArrayLen(expr, dim);
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
    public static _IExpression create_BoolBoundedPool() {
      return new Expression_BoolBoundedPool();
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
    public bool is_BoolBoundedPool { get { return this is Expression_BoolBoundedPool; } }
    public bool is_IntRange { get { return this is Expression_IntRange; } }
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
    public DAST._IExpression dtor_length {
      get {
        var d = this;
        return ((Expression_SeqConstruct)d)._length;
      }
    }
    public DAST._IExpression dtor_elem {
      get {
        var d = this;
        return ((Expression_SeqConstruct)d)._elem;
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
    public BigInteger dtor_dim {
      get {
        var d = this;
        return ((Expression_ArrayLen)d)._dim;
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
    public DAST._IExpression dtor_lo {
      get {
        var d = this;
        return ((Expression_IntRange)d)._lo;
      }
    }
    public DAST._IExpression dtor_hi {
      get {
        var d = this;
        return ((Expression_IntRange)d)._hi;
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
  public class Expression_SeqConstruct : Expression {
    public readonly DAST._IExpression _length;
    public readonly DAST._IExpression _elem;
    public Expression_SeqConstruct(DAST._IExpression length, DAST._IExpression elem) : base() {
      this._length = length;
      this._elem = elem;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_SeqConstruct(_length, _elem);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_SeqConstruct;
      return oth != null && object.Equals(this._length, oth._length) && object.Equals(this._elem, oth._elem);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._length));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._elem));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.SeqConstruct";
      s += "(";
      s += Dafny.Helpers.ToString(this._length);
      s += ", ";
      s += Dafny.Helpers.ToString(this._elem);
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
      hash = ((hash << 5) + hash) + 9;
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
      hash = ((hash << 5) + hash) + 10;
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
      hash = ((hash << 5) + hash) + 11;
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
      hash = ((hash << 5) + hash) + 12;
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
      hash = ((hash << 5) + hash) + 13;
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
      hash = ((hash << 5) + hash) + 14;
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
      hash = ((hash << 5) + hash) + 15;
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
    public readonly BigInteger _dim;
    public Expression_ArrayLen(DAST._IExpression expr, BigInteger dim) : base() {
      this._expr = expr;
      this._dim = dim;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_ArrayLen(_expr, _dim);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_ArrayLen;
      return oth != null && object.Equals(this._expr, oth._expr) && this._dim == oth._dim;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 16;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._dim));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.ArrayLen";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._dim);
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
      hash = ((hash << 5) + hash) + 17;
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
      hash = ((hash << 5) + hash) + 18;
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
      hash = ((hash << 5) + hash) + 19;
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
      hash = ((hash << 5) + hash) + 20;
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
      hash = ((hash << 5) + hash) + 21;
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
      hash = ((hash << 5) + hash) + 22;
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
      hash = ((hash << 5) + hash) + 23;
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
      hash = ((hash << 5) + hash) + 24;
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
      hash = ((hash << 5) + hash) + 25;
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
      hash = ((hash << 5) + hash) + 26;
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
      hash = ((hash << 5) + hash) + 27;
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
      hash = ((hash << 5) + hash) + 28;
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
      hash = ((hash << 5) + hash) + 29;
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.BoolBoundedPool";
      return s;
    }
  }
  public class Expression_IntRange : Expression {
    public readonly DAST._IExpression _lo;
    public readonly DAST._IExpression _hi;
    public Expression_IntRange(DAST._IExpression lo, DAST._IExpression hi) : base() {
      this._lo = lo;
      this._hi = hi;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_IntRange(_lo, _hi);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_IntRange;
      return oth != null && object.Equals(this._lo, oth._lo) && object.Equals(this._hi, oth._hi);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 30;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._lo));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._hi));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.IntRange";
      s += "(";
      s += Dafny.Helpers.ToString(this._lo);
      s += ", ";
      s += Dafny.Helpers.ToString(this._hi);
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
            BigInteger _51___mcc_h18 = _source2.dtor_dims;
          } else if (_source2.is_Seq) {
            DAST._IType _52___mcc_h21 = _source2.dtor_element;
          } else if (_source2.is_Set) {
            DAST._IType _53___mcc_h23 = _source2.dtor_element;
          } else if (_source2.is_Multiset) {
            DAST._IType _54___mcc_h25 = _source2.dtor_element;
          } else if (_source2.is_Map) {
            DAST._IType _55___mcc_h27 = _source2.dtor_key;
            DAST._IType _56___mcc_h28 = _source2.dtor_value;
          } else if (_source2.is_Arrow) {
            Dafny.ISequence<DAST._IType> _57___mcc_h31 = _source2.dtor_args;
            DAST._IType _58___mcc_h32 = _source2.dtor_result;
          } else if (_source2.is_Primitive) {
            DAST._IPrimitive _59___mcc_h35 = _source2.dtor_Primitive_a0;
          } else if (_source2.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _60___mcc_h37 = _source2.dtor_Passthrough_a0;
          } else {
            Dafny.ISequence<Dafny.Rune> _61___mcc_h39 = _source2.dtor_TypeArg_a0;
          }
          _34_i = (_34_i) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.Rune> _62_defaultImpl;
      _62_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _18_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::std::default::Default for r#")), (c).dtor_name), _17_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      _62_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(_62_defaultImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn default() -> Self {\n"));
      _62_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_62_defaultImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new()\n"));
      _62_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(_62_defaultImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      _62_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(_62_defaultImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      Dafny.ISequence<Dafny.Rune> _63_printImpl;
      _63_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _18_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyPrint for r#")), (c).dtor_name), _17_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {\n"));
      _63_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_63_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(__fmt_print_formatter, \"")), ((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")\n}\n}\n"));
      Dafny.ISequence<Dafny.Rune> _64_ptrPartialEqImpl;
      _64_ptrPartialEqImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _18_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::std::cmp::PartialEq for r#")), (c).dtor_name), _17_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      _64_ptrPartialEqImpl = Dafny.Sequence<Dafny.Rune>.Concat(_64_ptrPartialEqImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn eq(&self, other: &Self) -> bool {\n"));
      _64_ptrPartialEqImpl = Dafny.Sequence<Dafny.Rune>.Concat(_64_ptrPartialEqImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ptr::eq(self, other)"));
      _64_ptrPartialEqImpl = Dafny.Sequence<Dafny.Rune>.Concat(_64_ptrPartialEqImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}\n}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _62_defaultImpl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _63_printImpl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _64_ptrPartialEqImpl);
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
          DCOMP.COMP.GenExpr(_78_e, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None(), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), true, out _out28, out _out29, out _out30, out _out31);
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
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _131___mcc_h18 = _source6.dtor_path;
            {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc<"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            }
          } else if (_source6.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _132___mcc_h20 = _source6.dtor_path;
            {
              if (inBinding) {
                s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_");
              } else {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              }
            }
          } else {
            DAST._IType _133___mcc_h22 = _source6.dtor_Newtype_a0;
            DAST._IResolvedType _134_Primitive = _127_resolved;
          }
        }
      } else if (_source5.is_Nullable) {
        DAST._IType _135___mcc_h3 = _source5.dtor_Nullable_a0;
        DAST._IType _136_inner = _135___mcc_h3;
        {
          Dafny.ISequence<Dafny.Rune> _137_innerStr;
          Dafny.ISequence<Dafny.Rune> _out43;
          _out43 = DCOMP.COMP.GenType(_136_inner, inBinding, inFn);
          _137_innerStr = _out43;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::option::Option<"), _137_innerStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
        }
      } else if (_source5.is_Tuple) {
        Dafny.ISequence<DAST._IType> _138___mcc_h4 = _source5.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IType> _139_types = _138___mcc_h4;
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
          BigInteger _140_i;
          _140_i = BigInteger.Zero;
          while ((_140_i) < (new BigInteger((_139_types).Count))) {
            if ((_140_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
            }
            Dafny.ISequence<Dafny.Rune> _141_generated;
            Dafny.ISequence<Dafny.Rune> _out44;
            _out44 = DCOMP.COMP.GenType((_139_types).Select(_140_i), inBinding, inFn);
            _141_generated = _out44;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _141_generated), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
            _140_i = (_140_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        }
      } else if (_source5.is_Array) {
        DAST._IType _142___mcc_h5 = _source5.dtor_element;
        BigInteger _143___mcc_h6 = _source5.dtor_dims;
        BigInteger _144_dims = _143___mcc_h6;
        DAST._IType _145_element = _142___mcc_h5;
        {
          Dafny.ISequence<Dafny.Rune> _146_elemStr;
          Dafny.ISequence<Dafny.Rune> _out45;
          _out45 = DCOMP.COMP.GenType(_145_element, inBinding, inFn);
          _146_elemStr = _out45;
          s = _146_elemStr;
          BigInteger _147_i;
          _147_i = BigInteger.Zero;
          while ((_147_i) < (_144_dims)) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc<::std::cell::RefCell<::std::vec::Vec<"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>>"));
            _147_i = (_147_i) + (BigInteger.One);
          }
        }
      } else if (_source5.is_Seq) {
        DAST._IType _148___mcc_h7 = _source5.dtor_element;
        DAST._IType _149_element = _148___mcc_h7;
        {
          Dafny.ISequence<Dafny.Rune> _150_elemStr;
          Dafny.ISequence<Dafny.Rune> _out46;
          _out46 = DCOMP.COMP.GenType(_149_element, inBinding, inFn);
          _150_elemStr = _out46;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::vec::Vec<"), _150_elemStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
        }
      } else if (_source5.is_Set) {
        DAST._IType _151___mcc_h8 = _source5.dtor_element;
        DAST._IType _152_element = _151___mcc_h8;
        {
          Dafny.ISequence<Dafny.Rune> _153_elemStr;
          Dafny.ISequence<Dafny.Rune> _out47;
          _out47 = DCOMP.COMP.GenType(_152_element, inBinding, inFn);
          _153_elemStr = _out47;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::collections::HashSet<"), _153_elemStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
        }
      } else if (_source5.is_Multiset) {
        DAST._IType _154___mcc_h9 = _source5.dtor_element;
        DAST._IType _155_element = _154___mcc_h9;
        {
          Dafny.ISequence<Dafny.Rune> _156_elemStr;
          Dafny.ISequence<Dafny.Rune> _out48;
          _out48 = DCOMP.COMP.GenType(_155_element, inBinding, inFn);
          _156_elemStr = _out48;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::collections::HashMap<"), _156_elemStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", u64>"));
        }
      } else if (_source5.is_Map) {
        DAST._IType _157___mcc_h10 = _source5.dtor_key;
        DAST._IType _158___mcc_h11 = _source5.dtor_value;
        DAST._IType _159_value = _158___mcc_h11;
        DAST._IType _160_key = _157___mcc_h10;
        {
          Dafny.ISequence<Dafny.Rune> _161_keyStr;
          Dafny.ISequence<Dafny.Rune> _out49;
          _out49 = DCOMP.COMP.GenType(_160_key, inBinding, inFn);
          _161_keyStr = _out49;
          Dafny.ISequence<Dafny.Rune> _162_valueStr;
          Dafny.ISequence<Dafny.Rune> _out50;
          _out50 = DCOMP.COMP.GenType(_159_value, inBinding, inFn);
          _162_valueStr = _out50;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::collections::HashMap<"), _161_keyStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _162_valueStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
        }
      } else if (_source5.is_Arrow) {
        Dafny.ISequence<DAST._IType> _163___mcc_h12 = _source5.dtor_args;
        DAST._IType _164___mcc_h13 = _source5.dtor_result;
        DAST._IType _165_result = _164___mcc_h13;
        Dafny.ISequence<DAST._IType> _166_args = _163___mcc_h12;
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper<::std::rc::Rc<dyn ::std::ops::Fn(");
          BigInteger _167_i;
          _167_i = BigInteger.Zero;
          while ((_167_i) < (new BigInteger((_166_args).Count))) {
            if ((_167_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _168_generated;
            Dafny.ISequence<Dafny.Rune> _out51;
            _out51 = DCOMP.COMP.GenType((_166_args).Select(_167_i), inBinding, true);
            _168_generated = _out51;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")), _168_generated);
            _167_i = (_167_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _169_resultType;
          Dafny.ISequence<Dafny.Rune> _out52;
          _out52 = DCOMP.COMP.GenType(_165_result, inBinding, (inFn) || (inBinding));
          _169_resultType = _out52;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), _169_resultType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" + 'static>>"));
        }
      } else if (_source5.is_Primitive) {
        DAST._IPrimitive _170___mcc_h14 = _source5.dtor_Primitive_a0;
        DAST._IPrimitive _171_p = _170___mcc_h14;
        {
          DAST._IPrimitive _source7 = _171_p;
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
        Dafny.ISequence<Dafny.Rune> _172___mcc_h15 = _source5.dtor_Passthrough_a0;
        Dafny.ISequence<Dafny.Rune> _173_v = _172___mcc_h15;
        s = _173_v;
      } else {
        Dafny.ISequence<Dafny.Rune> _174___mcc_h16 = _source5.dtor_TypeArg_a0;
        Dafny.ISequence<Dafny.Rune> _source8 = _174___mcc_h16;
        Dafny.ISequence<Dafny.Rune> _175___mcc_h17 = _source8;
        Dafny.ISequence<Dafny.Rune> _176_name = _175___mcc_h17;
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _176_name);
      }
      return s;
    }
    public static void GenClassImplBody(Dafny.ISequence<DAST._IMethod> body, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams, out Dafny.ISequence<Dafny.Rune> s, out Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> traitBodies) {
      s = Dafny.Sequence<Dafny.Rune>.Empty;
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _177_i;
      _177_i = BigInteger.Zero;
      while ((_177_i) < (new BigInteger((body).Count))) {
        DAST._IMethod _source9 = (body).Select(_177_i);
        DAST._IMethod _178___mcc_h0 = _source9;
        DAST._IMethod _179_m = _178___mcc_h0;
        {
          DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source10 = (_179_m).dtor_overridingPath;
          if (_source10.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _180___mcc_h1 = _source10.dtor_Some_a0;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _181_p = _180___mcc_h1;
            {
              Dafny.ISequence<Dafny.Rune> _182_existing;
              _182_existing = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              if ((traitBodies).Contains(_181_p)) {
                _182_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Select(traitBodies, _181_p);
              }
              if ((new BigInteger((_182_existing).Count)).Sign == 1) {
                _182_existing = Dafny.Sequence<Dafny.Rune>.Concat(_182_existing, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
              }
              Dafny.ISequence<Dafny.Rune> _183_genMethod;
              Dafny.ISequence<Dafny.Rune> _out53;
              _out53 = DCOMP.COMP.GenMethod(_179_m, true, enclosingType, enclosingTypeParams);
              _183_genMethod = _out53;
              _182_existing = Dafny.Sequence<Dafny.Rune>.Concat(_182_existing, _183_genMethod);
              traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>(_181_p, _182_existing)));
            }
          } else {
            {
              Dafny.ISequence<Dafny.Rune> _184_generated;
              Dafny.ISequence<Dafny.Rune> _out54;
              _out54 = DCOMP.COMP.GenMethod(_179_m, forTrait, enclosingType, enclosingTypeParams);
              _184_generated = _out54;
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, _184_generated);
            }
          }
        }
        if ((new BigInteger((s).Count)).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        _177_i = (_177_i) + (BigInteger.One);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> GenParams(Dafny.ISequence<DAST._IFormal> @params) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _185_i;
      _185_i = BigInteger.Zero;
      while ((_185_i) < (new BigInteger((@params).Count))) {
        DAST._IFormal _186_param;
        _186_param = (@params).Select(_185_i);
        Dafny.ISequence<Dafny.Rune> _187_paramType;
        Dafny.ISequence<Dafny.Rune> _out55;
        _out55 = DCOMP.COMP.GenType((_186_param).dtor_typ, false, false);
        _187_paramType = _out55;
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_186_param).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": &")), _187_paramType);
        if ((_185_i) < ((new BigInteger((@params).Count)) - (BigInteger.One))) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
        }
        _185_i = (_185_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISequence<Dafny.Rune> _188_params;
      Dafny.ISequence<Dafny.Rune> _out56;
      _out56 = DCOMP.COMP.GenParams((m).dtor_params);
      _188_params = _out56;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _189_paramNames;
      _189_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _190_paramI;
      _190_paramI = BigInteger.Zero;
      while ((_190_paramI) < (new BigInteger(((m).dtor_params).Count))) {
        _189_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_189_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((((m).dtor_params).Select(_190_paramI)).dtor_name));
        _190_paramI = (_190_paramI) + (BigInteger.One);
      }
      if (!((m).dtor_isStatic)) {
        if (forTrait) {
          _188_params = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _188_params);
        } else {
          Dafny.ISequence<Dafny.Rune> _191_enclosingTypeString;
          Dafny.ISequence<Dafny.Rune> _out57;
          _out57 = DCOMP.COMP.GenType(enclosingType, false, false);
          _191_enclosingTypeString = _out57;
          _188_params = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self: &"), _191_enclosingTypeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _188_params);
        }
      }
      Dafny.ISequence<Dafny.Rune> _192_retType;
      _192_retType = (((new BigInteger(((m).dtor_outTypes).Count)) != (BigInteger.One)) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
      BigInteger _193_typeI;
      _193_typeI = BigInteger.Zero;
      while ((_193_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        if ((_193_typeI).Sign == 1) {
          _192_retType = Dafny.Sequence<Dafny.Rune>.Concat(_192_retType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
        }
        Dafny.ISequence<Dafny.Rune> _194_typeString;
        Dafny.ISequence<Dafny.Rune> _out58;
        _out58 = DCOMP.COMP.GenType(((m).dtor_outTypes).Select(_193_typeI), false, false);
        _194_typeString = _out58;
        _192_retType = Dafny.Sequence<Dafny.Rune>.Concat(_192_retType, _194_typeString);
        _193_typeI = (_193_typeI) + (BigInteger.One);
      }
      if ((new BigInteger(((m).dtor_outTypes).Count)) != (BigInteger.One)) {
        _192_retType = Dafny.Sequence<Dafny.Rune>.Concat(_192_retType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      }
      if (forTrait) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn r#"), (m).dtor_name);
      } else {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub fn r#"), (m).dtor_name);
      }
      Dafny.ISequence<DAST._IType> _195_typeParamsFiltered;
      _195_typeParamsFiltered = Dafny.Sequence<DAST._IType>.FromElements();
      BigInteger _196_typeParamI;
      _196_typeParamI = BigInteger.Zero;
      while ((_196_typeParamI) < (new BigInteger(((m).dtor_typeParams).Count))) {
        DAST._IType _197_typeParam;
        _197_typeParam = ((m).dtor_typeParams).Select(_196_typeParamI);
        if (!((enclosingTypeParams).Contains(_197_typeParam))) {
          _195_typeParamsFiltered = Dafny.Sequence<DAST._IType>.Concat(_195_typeParamsFiltered, Dafny.Sequence<DAST._IType>.FromElements(_197_typeParam));
        }
        _196_typeParamI = (_196_typeParamI) + (BigInteger.One);
      }
      if ((new BigInteger((_195_typeParamsFiltered).Count)).Sign == 1) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"));
        BigInteger _198_i;
        _198_i = BigInteger.Zero;
        while ((_198_i) < (new BigInteger((_195_typeParamsFiltered).Count))) {
          if ((_198_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          Dafny.ISequence<Dafny.Rune> _199_typeString;
          Dafny.ISequence<Dafny.Rune> _out59;
          _out59 = DCOMP.COMP.GenType((_195_typeParamsFiltered).Select(_198_i), false, false);
          _199_typeString = _out59;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _199_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<")), _199_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("> + Clone + ::std::cmp::PartialEq + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static"));
          _198_i = (_198_i) + (BigInteger.One);
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _188_params), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), _192_retType);
      if ((m).dtor_hasBody) {
        Dafny.ISequence<Dafny.Rune> _200_earlyReturn;
        _200_earlyReturn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return;");
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source11 = (m).dtor_outVars;
        if (_source11.is_Some) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _201___mcc_h0 = _source11.dtor_Some_a0;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _202_outVars = _201___mcc_h0;
          {
            _200_earlyReturn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return (");
            BigInteger _203_outI;
            _203_outI = BigInteger.Zero;
            while ((_203_outI) < (new BigInteger((_202_outVars).Count))) {
              if ((_203_outI).Sign == 1) {
                _200_earlyReturn = Dafny.Sequence<Dafny.Rune>.Concat(_200_earlyReturn, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _204_outVar;
              _204_outVar = (_202_outVars).Select(_203_outI);
              _200_earlyReturn = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_200_earlyReturn, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_204_outVar));
              _203_outI = (_203_outI) + (BigInteger.One);
            }
            _200_earlyReturn = Dafny.Sequence<Dafny.Rune>.Concat(_200_earlyReturn, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");"));
          }
        } else {
        }
        Dafny.ISequence<Dafny.Rune> _205_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _206___v12;
        Dafny.ISequence<Dafny.Rune> _out60;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out61;
        DCOMP.COMP.GenStmts((m).dtor_body, (((m).dtor_isStatic) ? (DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None()) : (DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))), _189_paramNames, true, _200_earlyReturn, out _out60, out _out61);
        _205_body = _out60;
        _206___v12 = _out61;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source12 = (m).dtor_outVars;
        if (_source12.is_Some) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _207___mcc_h1 = _source12.dtor_Some_a0;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _208_outVars = _207___mcc_h1;
          {
            _205_body = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_205_body, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _200_earlyReturn);
          }
        } else {
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _205_body), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}\n"));
      } else {
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
      }
      return s;
    }
    public static void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DAST._IOptional<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, bool isLast, Dafny.ISequence<Dafny.Rune> earlyReturn, out Dafny.ISequence<Dafny.Rune> generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents) {
      generated = Dafny.Sequence<Dafny.Rune>.Empty;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _209_declarations;
      _209_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _210_i;
      _210_i = BigInteger.Zero;
      while ((_210_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _211_stmt;
        _211_stmt = (stmts).Select(_210_i);
        Dafny.ISequence<Dafny.Rune> _212_stmtString;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _213_recIdents;
        Dafny.ISequence<Dafny.Rune> _out62;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out63;
        DCOMP.COMP.GenStmt(_211_stmt, selfIdent, @params, (isLast) && ((_210_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out62, out _out63);
        _212_stmtString = _out62;
        _213_recIdents = _out63;
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_213_recIdents, _209_declarations));
        DAST._IStatement _source13 = _211_stmt;
        if (_source13.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _214___mcc_h0 = _source13.dtor_name;
          DAST._IType _215___mcc_h1 = _source13.dtor_typ;
          DAST._IOptional<DAST._IExpression> _216___mcc_h2 = _source13.dtor_maybeValue;
          Dafny.ISequence<Dafny.Rune> _217_name = _214___mcc_h0;
          {
            _209_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_209_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_217_name));
          }
        } else if (_source13.is_Assign) {
          DAST._IAssignLhs _218___mcc_h6 = _source13.dtor_lhs;
          DAST._IExpression _219___mcc_h7 = _source13.dtor_value;
        } else if (_source13.is_If) {
          DAST._IExpression _220___mcc_h10 = _source13.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _221___mcc_h11 = _source13.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _222___mcc_h12 = _source13.dtor_els;
        } else if (_source13.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _223___mcc_h16 = _source13.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _224___mcc_h17 = _source13.dtor_body;
        } else if (_source13.is_While) {
          DAST._IExpression _225___mcc_h20 = _source13.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _226___mcc_h21 = _source13.dtor_body;
        } else if (_source13.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _227___mcc_h24 = _source13.dtor_boundName;
          DAST._IType _228___mcc_h25 = _source13.dtor_boundType;
          DAST._IExpression _229___mcc_h26 = _source13.dtor_over;
          Dafny.ISequence<DAST._IStatement> _230___mcc_h27 = _source13.dtor_body;
        } else if (_source13.is_Call) {
          DAST._IExpression _231___mcc_h32 = _source13.dtor_on;
          Dafny.ISequence<Dafny.Rune> _232___mcc_h33 = _source13.dtor_name;
          Dafny.ISequence<DAST._IType> _233___mcc_h34 = _source13.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _234___mcc_h35 = _source13.dtor_args;
          DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _235___mcc_h36 = _source13.dtor_outs;
        } else if (_source13.is_Return) {
          DAST._IExpression _236___mcc_h42 = _source13.dtor_expr;
        } else if (_source13.is_EarlyReturn) {
        } else if (_source13.is_Break) {
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _237___mcc_h44 = _source13.dtor_toLabel;
        } else if (_source13.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _238___mcc_h46 = _source13.dtor_body;
        } else if (_source13.is_JumpTailCallStart) {
        } else if (_source13.is_Halt) {
        } else {
          DAST._IExpression _239___mcc_h48 = _source13.dtor_Print_a0;
        }
        if ((_210_i).Sign == 1) {
          generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, _212_stmtString);
        _210_i = (_210_i) + (BigInteger.One);
      }
    }
    public static void GenAssignLhs(DAST._IAssignLhs lhs, Dafny.ISequence<Dafny.Rune> rhs, DAST._IOptional<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, out Dafny.ISequence<Dafny.Rune> generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents) {
      generated = Dafny.Sequence<Dafny.Rune>.Empty;
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IAssignLhs _source14 = lhs;
      if (_source14.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _240___mcc_h0 = _source14.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _source15 = _240___mcc_h0;
        Dafny.ISequence<Dafny.Rune> _241___mcc_h1 = _source15;
        Dafny.ISequence<Dafny.Rune> _242_id = _241___mcc_h1;
        {
          if ((@params).Contains(_242_id)) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*r#"), _242_id);
          } else {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _242_id);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_242_id);
          needsIIFE = false;
        }
      } else if (_source14.is_Select) {
        DAST._IExpression _243___mcc_h2 = _source14.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _244___mcc_h3 = _source14.dtor_field;
        Dafny.ISequence<Dafny.Rune> _245_field = _244___mcc_h3;
        DAST._IExpression _246_on = _243___mcc_h2;
        {
          Dafny.ISequence<Dafny.Rune> _247_onExpr;
          bool _248_onOwned;
          bool _249_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _250_recIdents;
          Dafny.ISequence<Dafny.Rune> _out64;
          bool _out65;
          bool _out66;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out67;
          DCOMP.COMP.GenExpr(_246_on, selfIdent, @params, false, out _out64, out _out65, out _out66, out _out67);
          _247_onExpr = _out64;
          _248_onOwned = _out65;
          _249_onErased = _out66;
          _250_recIdents = _out67;
          if (!(_249_onErased)) {
            Dafny.ISequence<Dafny.Rune> _251_eraseFn;
            _251_eraseFn = ((_248_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _247_onExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _251_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _247_onExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*("), _247_onExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _245_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()) = ")), rhs), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          readIdents = _250_recIdents;
          needsIIFE = true;
        }
      } else {
        DAST._IExpression _252___mcc_h4 = _source14.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _253___mcc_h5 = _source14.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _254_indices = _253___mcc_h5;
        DAST._IExpression _255_on = _252___mcc_h4;
        {
          Dafny.ISequence<Dafny.Rune> _256_onExpr;
          bool _257_onOwned;
          bool _258_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _259_recIdents;
          Dafny.ISequence<Dafny.Rune> _out68;
          bool _out69;
          bool _out70;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out71;
          DCOMP.COMP.GenExpr(_255_on, selfIdent, @params, false, out _out68, out _out69, out _out70, out _out71);
          _256_onExpr = _out68;
          _257_onOwned = _out69;
          _258_onErased = _out70;
          _259_recIdents = _out71;
          readIdents = _259_recIdents;
          if (!(_258_onErased)) {
            Dafny.ISequence<Dafny.Rune> _260_eraseFn;
            _260_eraseFn = ((_257_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _256_onExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _260_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _256_onExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          BigInteger _261_i;
          _261_i = BigInteger.Zero;
          while ((_261_i) < (new BigInteger((_254_indices).Count))) {
            Dafny.ISequence<Dafny.Rune> _262_idx;
            bool _263___v16;
            bool _264_idxErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _265_recIdentsIdx;
            Dafny.ISequence<Dafny.Rune> _out72;
            bool _out73;
            bool _out74;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out75;
            DCOMP.COMP.GenExpr((_254_indices).Select(_261_i), selfIdent, @params, true, out _out72, out _out73, out _out74, out _out75);
            _262_idx = _out72;
            _263___v16 = _out73;
            _264_idxErased = _out74;
            _265_recIdentsIdx = _out75;
            if (!(_264_idxErased)) {
              _262_idx = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _262_idx), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let __idx")), DCOMP.__default.natToString(_261_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = <usize as ::dafny_runtime::NumCast>::from(")), _262_idx), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap();\n"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _265_recIdentsIdx);
            _261_i = (_261_i) + (BigInteger.One);
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, _256_onExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()"));
          _261_i = BigInteger.Zero;
          while ((_261_i) < (new BigInteger((_254_indices).Count))) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[__idx")), DCOMP.__default.natToString(_261_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
            _261_i = (_261_i) + (BigInteger.One);
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
        Dafny.ISequence<Dafny.Rune> _266___mcc_h0 = _source16.dtor_name;
        DAST._IType _267___mcc_h1 = _source16.dtor_typ;
        DAST._IOptional<DAST._IExpression> _268___mcc_h2 = _source16.dtor_maybeValue;
        DAST._IOptional<DAST._IExpression> _source17 = _268___mcc_h2;
        if (_source17.is_Some) {
          DAST._IExpression _269___mcc_h3 = _source17.dtor_Some_a0;
          DAST._IExpression _270_expression = _269___mcc_h3;
          DAST._IType _271_typ = _267___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _272_name = _266___mcc_h0;
          {
            Dafny.ISequence<Dafny.Rune> _273_expr;
            bool _274___v17;
            bool _275_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _276_recIdents;
            Dafny.ISequence<Dafny.Rune> _out76;
            bool _out77;
            bool _out78;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out79;
            DCOMP.COMP.GenExpr(_270_expression, selfIdent, @params, true, out _out76, out _out77, out _out78, out _out79);
            _273_expr = _out76;
            _274___v17 = _out77;
            _275_recErased = _out78;
            _276_recIdents = _out79;
            if (_275_recErased) {
              _273_expr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _273_expr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            Dafny.ISequence<Dafny.Rune> _277_typeString;
            Dafny.ISequence<Dafny.Rune> _out80;
            _out80 = DCOMP.COMP.GenType(_271_typ, true, false);
            _277_typeString = _out80;
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#"), _272_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _277_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _273_expr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            readIdents = _276_recIdents;
          }
        } else {
          DAST._IType _278_typ = _267___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _279_name = _266___mcc_h0;
          {
            Dafny.ISequence<Dafny.Rune> _280_typeString;
            Dafny.ISequence<Dafny.Rune> _out81;
            _out81 = DCOMP.COMP.GenType(_278_typ, true, false);
            _280_typeString = _out81;
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#"), _279_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _280_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        }
      } else if (_source16.is_Assign) {
        DAST._IAssignLhs _281___mcc_h4 = _source16.dtor_lhs;
        DAST._IExpression _282___mcc_h5 = _source16.dtor_value;
        DAST._IExpression _283_expression = _282___mcc_h5;
        DAST._IAssignLhs _284_lhs = _281___mcc_h4;
        {
          Dafny.ISequence<Dafny.Rune> _285_lhsGen;
          bool _286_needsIIFE;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _287_recIdents;
          Dafny.ISequence<Dafny.Rune> _out82;
          bool _out83;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out84;
          DCOMP.COMP.GenAssignLhs(_284_lhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__rhs"), selfIdent, @params, out _out82, out _out83, out _out84);
          _285_lhsGen = _out82;
          _286_needsIIFE = _out83;
          _287_recIdents = _out84;
          Dafny.ISequence<Dafny.Rune> _288_exprGen;
          bool _289___v18;
          bool _290_exprErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _291_exprIdents;
          Dafny.ISequence<Dafny.Rune> _out85;
          bool _out86;
          bool _out87;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out88;
          DCOMP.COMP.GenExpr(_283_expression, selfIdent, @params, true, out _out85, out _out86, out _out87, out _out88);
          _288_exprGen = _out85;
          _289___v18 = _out86;
          _290_exprErased = _out87;
          _291_exprIdents = _out88;
          if (_290_exprErased) {
            _288_exprGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _288_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (_286_needsIIFE) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet __rhs = "), _288_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n")), _285_lhsGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
          } else {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_285_lhsGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _288_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_287_recIdents, _291_exprIdents);
        }
      } else if (_source16.is_If) {
        DAST._IExpression _292___mcc_h6 = _source16.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _293___mcc_h7 = _source16.dtor_thn;
        Dafny.ISequence<DAST._IStatement> _294___mcc_h8 = _source16.dtor_els;
        Dafny.ISequence<DAST._IStatement> _295_els = _294___mcc_h8;
        Dafny.ISequence<DAST._IStatement> _296_thn = _293___mcc_h7;
        DAST._IExpression _297_cond = _292___mcc_h6;
        {
          Dafny.ISequence<Dafny.Rune> _298_condString;
          bool _299___v19;
          bool _300_condErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _301_recIdents;
          Dafny.ISequence<Dafny.Rune> _out89;
          bool _out90;
          bool _out91;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out92;
          DCOMP.COMP.GenExpr(_297_cond, selfIdent, @params, true, out _out89, out _out90, out _out91, out _out92);
          _298_condString = _out89;
          _299___v19 = _out90;
          _300_condErased = _out91;
          _301_recIdents = _out92;
          if (!(_300_condErased)) {
            _298_condString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _298_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          readIdents = _301_recIdents;
          Dafny.ISequence<Dafny.Rune> _302_thnString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _303_thnIdents;
          Dafny.ISequence<Dafny.Rune> _out93;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out94;
          DCOMP.COMP.GenStmts(_296_thn, selfIdent, @params, isLast, earlyReturn, out _out93, out _out94);
          _302_thnString = _out93;
          _303_thnIdents = _out94;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _303_thnIdents);
          Dafny.ISequence<Dafny.Rune> _304_elsString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _305_elsIdents;
          Dafny.ISequence<Dafny.Rune> _out95;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out96;
          DCOMP.COMP.GenStmts(_295_els, selfIdent, @params, isLast, earlyReturn, out _out95, out _out96);
          _304_elsString = _out95;
          _305_elsIdents = _out96;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _305_elsIdents);
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if "), _298_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _302_thnString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _304_elsString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
        }
      } else if (_source16.is_Labeled) {
        Dafny.ISequence<Dafny.Rune> _306___mcc_h9 = _source16.dtor_lbl;
        Dafny.ISequence<DAST._IStatement> _307___mcc_h10 = _source16.dtor_body;
        Dafny.ISequence<DAST._IStatement> _308_body = _307___mcc_h10;
        Dafny.ISequence<Dafny.Rune> _309_lbl = _306___mcc_h9;
        {
          Dafny.ISequence<Dafny.Rune> _310_bodyString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _311_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out97;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out98;
          DCOMP.COMP.GenStmts(_308_body, selfIdent, @params, isLast, earlyReturn, out _out97, out _out98);
          _310_bodyString = _out97;
          _311_bodyIdents = _out98;
          readIdents = _311_bodyIdents;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'label_"), _309_lbl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": loop {\n")), _310_bodyString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break;")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
        }
      } else if (_source16.is_While) {
        DAST._IExpression _312___mcc_h11 = _source16.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _313___mcc_h12 = _source16.dtor_body;
        Dafny.ISequence<DAST._IStatement> _314_body = _313___mcc_h12;
        DAST._IExpression _315_cond = _312___mcc_h11;
        {
          Dafny.ISequence<Dafny.Rune> _316_condString;
          bool _317___v20;
          bool _318_condErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _319_recIdents;
          Dafny.ISequence<Dafny.Rune> _out99;
          bool _out100;
          bool _out101;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out102;
          DCOMP.COMP.GenExpr(_315_cond, selfIdent, @params, true, out _out99, out _out100, out _out101, out _out102);
          _316_condString = _out99;
          _317___v20 = _out100;
          _318_condErased = _out101;
          _319_recIdents = _out102;
          if (!(_318_condErased)) {
            _316_condString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase("), _316_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          readIdents = _319_recIdents;
          Dafny.ISequence<Dafny.Rune> _320_bodyString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _321_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out103;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out104;
          DCOMP.COMP.GenStmts(_314_body, selfIdent, @params, false, earlyReturn, out _out103, out _out104);
          _320_bodyString = _out103;
          _321_bodyIdents = _out104;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _321_bodyIdents);
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while "), _316_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _320_bodyString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
        }
      } else if (_source16.is_Foreach) {
        Dafny.ISequence<Dafny.Rune> _322___mcc_h13 = _source16.dtor_boundName;
        DAST._IType _323___mcc_h14 = _source16.dtor_boundType;
        DAST._IExpression _324___mcc_h15 = _source16.dtor_over;
        Dafny.ISequence<DAST._IStatement> _325___mcc_h16 = _source16.dtor_body;
        Dafny.ISequence<DAST._IStatement> _326_body = _325___mcc_h16;
        DAST._IExpression _327_over = _324___mcc_h15;
        DAST._IType _328_boundType = _323___mcc_h14;
        Dafny.ISequence<Dafny.Rune> _329_boundName = _322___mcc_h13;
        {
          Dafny.ISequence<Dafny.Rune> _330_overString;
          bool _331___v21;
          bool _332_overErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _333_recIdents;
          Dafny.ISequence<Dafny.Rune> _out105;
          bool _out106;
          bool _out107;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out108;
          DCOMP.COMP.GenExpr(_327_over, selfIdent, @params, true, out _out105, out _out106, out _out107, out _out108);
          _330_overString = _out105;
          _331___v21 = _out106;
          _332_overErased = _out107;
          _333_recIdents = _out108;
          if (!(_332_overErased)) {
            _330_overString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase("), _330_overString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          Dafny.ISequence<Dafny.Rune> _334_boundTypeStr;
          Dafny.ISequence<Dafny.Rune> _out109;
          _out109 = DCOMP.COMP.GenType(_328_boundType, false, false);
          _334_boundTypeStr = _out109;
          readIdents = _333_recIdents;
          Dafny.ISequence<Dafny.Rune> _335_bodyString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _336_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out110;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out111;
          DCOMP.COMP.GenStmts(_326_body, selfIdent, @params, false, earlyReturn, out _out110, out _out111);
          _335_bodyString = _out110;
          _336_bodyIdents = _out111;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _336_bodyIdents);
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("for _iter_erased in "), _330_overString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), _329_boundName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = <")), _334_boundTypeStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::unerase_owned(_iter_erased);\n")), _335_bodyString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
        }
      } else if (_source16.is_Call) {
        DAST._IExpression _337___mcc_h17 = _source16.dtor_on;
        Dafny.ISequence<Dafny.Rune> _338___mcc_h18 = _source16.dtor_name;
        Dafny.ISequence<DAST._IType> _339___mcc_h19 = _source16.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _340___mcc_h20 = _source16.dtor_args;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _341___mcc_h21 = _source16.dtor_outs;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _342_maybeOutVars = _341___mcc_h21;
        Dafny.ISequence<DAST._IExpression> _343_args = _340___mcc_h20;
        Dafny.ISequence<DAST._IType> _344_typeArgs = _339___mcc_h19;
        Dafny.ISequence<Dafny.Rune> _345_name = _338___mcc_h18;
        DAST._IExpression _346_on = _337___mcc_h17;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _347_typeArgString;
          _347_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_344_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _348_typeI;
            _348_typeI = BigInteger.Zero;
            _347_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<");
            while ((_348_typeI) < (new BigInteger((_344_typeArgs).Count))) {
              if ((_348_typeI).Sign == 1) {
                _347_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_347_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _349_typeString;
              Dafny.ISequence<Dafny.Rune> _out112;
              _out112 = DCOMP.COMP.GenType((_344_typeArgs).Select(_348_typeI), false, false);
              _349_typeString = _out112;
              _347_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_347_typeArgString, _349_typeString);
              _348_typeI = (_348_typeI) + (BigInteger.One);
            }
            _347_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_347_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
          Dafny.ISequence<Dafny.Rune> _350_argString;
          _350_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _351_i;
          _351_i = BigInteger.Zero;
          while ((_351_i) < (new BigInteger((_343_args).Count))) {
            if ((_351_i).Sign == 1) {
              _350_argString = Dafny.Sequence<Dafny.Rune>.Concat(_350_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _352_argExpr;
            bool _353_isOwned;
            bool _354_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _355_argIdents;
            Dafny.ISequence<Dafny.Rune> _out113;
            bool _out114;
            bool _out115;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
            DCOMP.COMP.GenExpr((_343_args).Select(_351_i), selfIdent, @params, false, out _out113, out _out114, out _out115, out _out116);
            _352_argExpr = _out113;
            _353_isOwned = _out114;
            _354_argErased = _out115;
            _355_argIdents = _out116;
            if (_353_isOwned) {
              _352_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _352_argExpr);
            }
            _350_argString = Dafny.Sequence<Dafny.Rune>.Concat(_350_argString, _352_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _355_argIdents);
            _351_i = (_351_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _356_enclosingString;
          bool _357___v22;
          bool _358___v23;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _359_enclosingIdents;
          Dafny.ISequence<Dafny.Rune> _out117;
          bool _out118;
          bool _out119;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out120;
          DCOMP.COMP.GenExpr(_346_on, selfIdent, @params, false, out _out117, out _out118, out _out119, out _out120);
          _356_enclosingString = _out117;
          _357___v22 = _out118;
          _358___v23 = _out119;
          _359_enclosingIdents = _out120;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _359_enclosingIdents);
          DAST._IExpression _source18 = _346_on;
          if (_source18.is_Literal) {
            DAST._ILiteral _360___mcc_h26 = _source18.dtor_Literal_a0;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _361___mcc_h28 = _source18.dtor_Ident_a0;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _362___mcc_h30 = _source18.dtor_Companion_a0;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(_356_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
            }
          } else if (_source18.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _363___mcc_h32 = _source18.dtor_Tuple_a0;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _364___mcc_h34 = _source18.dtor_path;
            Dafny.ISequence<DAST._IExpression> _365___mcc_h35 = _source18.dtor_args;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _366___mcc_h38 = _source18.dtor_dims;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _367___mcc_h40 = _source18.dtor_path;
            Dafny.ISequence<Dafny.Rune> _368___mcc_h41 = _source18.dtor_variant;
            bool _369___mcc_h42 = _source18.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _370___mcc_h43 = _source18.dtor_contents;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Convert) {
            DAST._IExpression _371___mcc_h48 = _source18.dtor_value;
            DAST._IType _372___mcc_h49 = _source18.dtor_from;
            DAST._IType _373___mcc_h50 = _source18.dtor_typ;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_SeqConstruct) {
            DAST._IExpression _374___mcc_h54 = _source18.dtor_length;
            DAST._IExpression _375___mcc_h55 = _source18.dtor_elem;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _376___mcc_h58 = _source18.dtor_elements;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _377___mcc_h60 = _source18.dtor_elements;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_MapValue) {
            Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _378___mcc_h62 = _source18.dtor_mapElems;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_This) {
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Ite) {
            DAST._IExpression _379___mcc_h64 = _source18.dtor_cond;
            DAST._IExpression _380___mcc_h65 = _source18.dtor_thn;
            DAST._IExpression _381___mcc_h66 = _source18.dtor_els;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_UnOp) {
            DAST._IUnaryOp _382___mcc_h70 = _source18.dtor_unOp;
            DAST._IExpression _383___mcc_h71 = _source18.dtor_expr;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_BinOp) {
            Dafny.ISequence<Dafny.Rune> _384___mcc_h74 = _source18.dtor_op;
            DAST._IExpression _385___mcc_h75 = _source18.dtor_left;
            DAST._IExpression _386___mcc_h76 = _source18.dtor_right;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_ArrayLen) {
            DAST._IExpression _387___mcc_h80 = _source18.dtor_expr;
            BigInteger _388___mcc_h81 = _source18.dtor_dim;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Select) {
            DAST._IExpression _389___mcc_h84 = _source18.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _390___mcc_h85 = _source18.dtor_field;
            bool _391___mcc_h86 = _source18.dtor_isConstant;
            bool _392___mcc_h87 = _source18.dtor_onDatatype;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_SelectFn) {
            DAST._IExpression _393___mcc_h92 = _source18.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _394___mcc_h93 = _source18.dtor_field;
            bool _395___mcc_h94 = _source18.dtor_onDatatype;
            bool _396___mcc_h95 = _source18.dtor_isStatic;
            BigInteger _397___mcc_h96 = _source18.dtor_arity;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Index) {
            DAST._IExpression _398___mcc_h102 = _source18.dtor_expr;
            DAST._ICollKind _399___mcc_h103 = _source18.dtor_collKind;
            Dafny.ISequence<DAST._IExpression> _400___mcc_h104 = _source18.dtor_indices;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_IndexRange) {
            DAST._IExpression _401___mcc_h108 = _source18.dtor_expr;
            bool _402___mcc_h109 = _source18.dtor_isArray;
            DAST._IOptional<DAST._IExpression> _403___mcc_h110 = _source18.dtor_low;
            DAST._IOptional<DAST._IExpression> _404___mcc_h111 = _source18.dtor_high;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_TupleSelect) {
            DAST._IExpression _405___mcc_h116 = _source18.dtor_expr;
            BigInteger _406___mcc_h117 = _source18.dtor_index;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Call) {
            DAST._IExpression _407___mcc_h120 = _source18.dtor_on;
            Dafny.ISequence<Dafny.Rune> _408___mcc_h121 = _source18.dtor_name;
            Dafny.ISequence<DAST._IType> _409___mcc_h122 = _source18.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _410___mcc_h123 = _source18.dtor_args;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _411___mcc_h128 = _source18.dtor_params;
            DAST._IType _412___mcc_h129 = _source18.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _413___mcc_h130 = _source18.dtor_body;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _414___mcc_h134 = _source18.dtor_values;
            DAST._IType _415___mcc_h135 = _source18.dtor_retType;
            DAST._IExpression _416___mcc_h136 = _source18.dtor_expr;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _417___mcc_h140 = _source18.dtor_name;
            DAST._IType _418___mcc_h141 = _source18.dtor_typ;
            DAST._IExpression _419___mcc_h142 = _source18.dtor_value;
            DAST._IExpression _420___mcc_h143 = _source18.dtor_iifeBody;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Apply) {
            DAST._IExpression _421___mcc_h148 = _source18.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _422___mcc_h149 = _source18.dtor_args;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_TypeTest) {
            DAST._IExpression _423___mcc_h152 = _source18.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _424___mcc_h153 = _source18.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _425___mcc_h154 = _source18.dtor_variant;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_InitializationValue) {
            DAST._IType _426___mcc_h158 = _source18.dtor_typ;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_BoolBoundedPool) {
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else {
            DAST._IExpression _427___mcc_h160 = _source18.dtor_lo;
            DAST._IExpression _428___mcc_h161 = _source18.dtor_hi;
            {
              _356_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          }
          Dafny.ISequence<Dafny.Rune> _429_receiver;
          _429_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source19 = _342_maybeOutVars;
          if (_source19.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _430___mcc_h164 = _source19.dtor_Some_a0;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _431_outVars = _430___mcc_h164;
            {
              if ((new BigInteger((_431_outVars).Count)) > (BigInteger.One)) {
                _429_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
              }
              BigInteger _432_outI;
              _432_outI = BigInteger.Zero;
              while ((_432_outI) < (new BigInteger((_431_outVars).Count))) {
                if ((_432_outI).Sign == 1) {
                  _429_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_429_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                Dafny.ISequence<Dafny.Rune> _433_outVar;
                _433_outVar = (_431_outVars).Select(_432_outI);
                _429_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_429_receiver, (_433_outVar));
                _432_outI = (_432_outI) + (BigInteger.One);
              }
              if ((new BigInteger((_431_outVars).Count)) > (BigInteger.One)) {
                _429_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_429_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
            }
          } else {
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((!(_429_receiver).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_429_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), _356_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _345_name), _347_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _350_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");"));
        }
      } else if (_source16.is_Return) {
        DAST._IExpression _434___mcc_h22 = _source16.dtor_expr;
        DAST._IExpression _435_expr = _434___mcc_h22;
        {
          Dafny.ISequence<Dafny.Rune> _436_exprString;
          bool _437___v26;
          bool _438_recErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _439_recIdents;
          Dafny.ISequence<Dafny.Rune> _out121;
          bool _out122;
          bool _out123;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out124;
          DCOMP.COMP.GenExpr(_435_expr, selfIdent, @params, true, out _out121, out _out122, out _out123, out _out124);
          _436_exprString = _out121;
          _437___v26 = _out122;
          _438_recErased = _out123;
          _439_recIdents = _out124;
          _436_exprString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _436_exprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          readIdents = _439_recIdents;
          if (isLast) {
            generated = _436_exprString;
          } else {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return "), _436_exprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          }
        }
      } else if (_source16.is_EarlyReturn) {
        {
          generated = earlyReturn;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source16.is_Break) {
        DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _440___mcc_h23 = _source16.dtor_toLabel;
        DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _441_toLabel = _440___mcc_h23;
        {
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _source20 = _441_toLabel;
          if (_source20.is_Some) {
            Dafny.ISequence<Dafny.Rune> _442___mcc_h165 = _source20.dtor_Some_a0;
            Dafny.ISequence<Dafny.Rune> _443_lbl = _442___mcc_h165;
            {
              generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break 'label_"), _443_lbl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            }
          } else {
            {
              generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break;");
            }
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source16.is_TailRecursive) {
        Dafny.ISequence<DAST._IStatement> _444___mcc_h24 = _source16.dtor_body;
        Dafny.ISequence<DAST._IStatement> _445_body = _444___mcc_h24;
        {
          generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if (!object.Equals(selfIdent, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None())) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#_this = self.clone();\n"));
          }
          BigInteger _446_paramI;
          _446_paramI = BigInteger.Zero;
          while ((_446_paramI) < (new BigInteger((@params).Count))) {
            Dafny.ISequence<Dafny.Rune> _447_param;
            _447_param = (@params).Select(_446_paramI);
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#")), _447_param), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _447_param), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
            _446_paramI = (_446_paramI) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _448_bodyString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _449_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out125;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
          DCOMP.COMP.GenStmts(_445_body, ((!object.Equals(selfIdent, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None())), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), false, earlyReturn, out _out125, out _out126);
          _448_bodyString = _out125;
          _449_bodyIdents = _out126;
          readIdents = _449_bodyIdents;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'TAIL_CALL_START: loop {\n")), _448_bodyString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
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
        DAST._IExpression _450___mcc_h25 = _source16.dtor_Print_a0;
        DAST._IExpression _451_e = _450___mcc_h25;
        {
          Dafny.ISequence<Dafny.Rune> _452_printedExpr;
          bool _453_isOwned;
          bool _454___v27;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _455_recIdents;
          Dafny.ISequence<Dafny.Rune> _out127;
          bool _out128;
          bool _out129;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out130;
          DCOMP.COMP.GenExpr(_451_e, selfIdent, @params, false, out _out127, out _out128, out _out129, out _out130);
          _452_printedExpr = _out127;
          _453_isOwned = _out128;
          _454___v27 = _out129;
          _455_recIdents = _out130;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper("), ((_453_isOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _452_printedExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("));"));
          readIdents = _455_recIdents;
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
        DAST._ILiteral _456___mcc_h0 = _source21.dtor_Literal_a0;
        DAST._ILiteral _source22 = _456___mcc_h0;
        if (_source22.is_BoolLiteral) {
          bool _457___mcc_h1 = _source22.dtor_BoolLiteral_a0;
          if ((_457___mcc_h1) == (false)) {
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
          Dafny.ISequence<Dafny.Rune> _458___mcc_h2 = _source22.dtor_IntLiteral_a0;
          DAST._IType _459___mcc_h3 = _source22.dtor_IntLiteral_a1;
          DAST._IType _460_t = _459___mcc_h3;
          Dafny.ISequence<Dafny.Rune> _461_i = _458___mcc_h2;
          {
            DAST._IType _source23 = _460_t;
            if (_source23.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _462___mcc_h215 = _source23.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _463___mcc_h216 = _source23.dtor_typeArgs;
              DAST._IResolvedType _464___mcc_h217 = _source23.dtor_resolved;
              {
                s = _461_i;
              }
            } else if (_source23.is_Nullable) {
              DAST._IType _465___mcc_h221 = _source23.dtor_Nullable_a0;
              {
                s = _461_i;
              }
            } else if (_source23.is_Tuple) {
              Dafny.ISequence<DAST._IType> _466___mcc_h223 = _source23.dtor_Tuple_a0;
              {
                s = _461_i;
              }
            } else if (_source23.is_Array) {
              DAST._IType _467___mcc_h225 = _source23.dtor_element;
              BigInteger _468___mcc_h226 = _source23.dtor_dims;
              {
                s = _461_i;
              }
            } else if (_source23.is_Seq) {
              DAST._IType _469___mcc_h229 = _source23.dtor_element;
              {
                s = _461_i;
              }
            } else if (_source23.is_Set) {
              DAST._IType _470___mcc_h231 = _source23.dtor_element;
              {
                s = _461_i;
              }
            } else if (_source23.is_Multiset) {
              DAST._IType _471___mcc_h233 = _source23.dtor_element;
              {
                s = _461_i;
              }
            } else if (_source23.is_Map) {
              DAST._IType _472___mcc_h235 = _source23.dtor_key;
              DAST._IType _473___mcc_h236 = _source23.dtor_value;
              {
                s = _461_i;
              }
            } else if (_source23.is_Arrow) {
              Dafny.ISequence<DAST._IType> _474___mcc_h239 = _source23.dtor_args;
              DAST._IType _475___mcc_h240 = _source23.dtor_result;
              {
                s = _461_i;
              }
            } else if (_source23.is_Primitive) {
              DAST._IPrimitive _476___mcc_h243 = _source23.dtor_Primitive_a0;
              DAST._IPrimitive _source24 = _476___mcc_h243;
              if (_source24.is_Int) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::parse_bytes(b\""), _461_i), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap()"));
                }
              } else if (_source24.is_Real) {
                {
                  s = _461_i;
                }
              } else if (_source24.is_String) {
                {
                  s = _461_i;
                }
              } else if (_source24.is_Bool) {
                {
                  s = _461_i;
                }
              } else {
                {
                  s = _461_i;
                }
              }
            } else if (_source23.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _477___mcc_h245 = _source23.dtor_Passthrough_a0;
              {
                s = _461_i;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _478___mcc_h247 = _source23.dtor_TypeArg_a0;
              {
                s = _461_i;
              }
            }
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source22.is_DecLiteral) {
          Dafny.ISequence<Dafny.Rune> _479___mcc_h4 = _source22.dtor_DecLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _480___mcc_h5 = _source22.dtor_DecLiteral_a1;
          DAST._IType _481___mcc_h6 = _source22.dtor_DecLiteral_a2;
          DAST._IType _482_t = _481___mcc_h6;
          Dafny.ISequence<Dafny.Rune> _483_d = _480___mcc_h5;
          Dafny.ISequence<Dafny.Rune> _484_n = _479___mcc_h4;
          {
            DAST._IType _source25 = _482_t;
            if (_source25.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _485___mcc_h249 = _source25.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _486___mcc_h250 = _source25.dtor_typeArgs;
              DAST._IResolvedType _487___mcc_h251 = _source25.dtor_resolved;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_484_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _483_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source25.is_Nullable) {
              DAST._IType _488___mcc_h255 = _source25.dtor_Nullable_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_484_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _483_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source25.is_Tuple) {
              Dafny.ISequence<DAST._IType> _489___mcc_h257 = _source25.dtor_Tuple_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_484_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _483_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source25.is_Array) {
              DAST._IType _490___mcc_h259 = _source25.dtor_element;
              BigInteger _491___mcc_h260 = _source25.dtor_dims;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_484_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _483_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source25.is_Seq) {
              DAST._IType _492___mcc_h263 = _source25.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_484_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _483_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source25.is_Set) {
              DAST._IType _493___mcc_h265 = _source25.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_484_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _483_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source25.is_Multiset) {
              DAST._IType _494___mcc_h267 = _source25.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_484_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _483_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source25.is_Map) {
              DAST._IType _495___mcc_h269 = _source25.dtor_key;
              DAST._IType _496___mcc_h270 = _source25.dtor_value;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_484_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _483_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source25.is_Arrow) {
              Dafny.ISequence<DAST._IType> _497___mcc_h273 = _source25.dtor_args;
              DAST._IType _498___mcc_h274 = _source25.dtor_result;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_484_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _483_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source25.is_Primitive) {
              DAST._IPrimitive _499___mcc_h277 = _source25.dtor_Primitive_a0;
              DAST._IPrimitive _source26 = _499___mcc_h277;
              if (_source26.is_Int) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_484_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _483_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else if (_source26.is_Real) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _484_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _483_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"));
                }
              } else if (_source26.is_String) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_484_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _483_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else if (_source26.is_Bool) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_484_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _483_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_484_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _483_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              }
            } else if (_source25.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _500___mcc_h279 = _source25.dtor_Passthrough_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_484_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _483_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _501___mcc_h281 = _source25.dtor_TypeArg_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_484_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _483_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            }
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source22.is_StringLiteral) {
          Dafny.ISequence<Dafny.Rune> _502___mcc_h7 = _source22.dtor_StringLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _503_l = _502___mcc_h7;
          {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\""), _503_l), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\".chars().collect::<Vec<char>>()"));
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source22.is_CharLiteral) {
          Dafny.Rune _504___mcc_h8 = _source22.dtor_CharLiteral_a0;
          Dafny.Rune _505_c = _504___mcc_h8;
          {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::primitive::char::from_u32("), DCOMP.__default.natToString(new BigInteger((_505_c).Value))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"));
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
        Dafny.ISequence<Dafny.Rune> _506___mcc_h9 = _source21.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _507_name = _506___mcc_h9;
        {
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _507_name);
          if (!((@params).Contains(_507_name))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(&"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
            isOwned = true;
          } else {
            isOwned = false;
          }
          isErased = false;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_507_name);
        }
      } else if (_source21.is_Companion) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _508___mcc_h10 = _source21.dtor_Companion_a0;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _509_path = _508___mcc_h10;
        {
          Dafny.ISequence<Dafny.Rune> _out131;
          _out131 = DCOMP.COMP.GenPath(_509_path);
          s = _out131;
          isOwned = true;
          isErased = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source21.is_Tuple) {
        Dafny.ISequence<DAST._IExpression> _510___mcc_h11 = _source21.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IExpression> _511_values = _510___mcc_h11;
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _512_i;
          _512_i = BigInteger.Zero;
          bool _513_allErased;
          _513_allErased = true;
          while ((_512_i) < (new BigInteger((_511_values).Count))) {
            Dafny.ISequence<Dafny.Rune> _514___v30;
            bool _515___v31;
            bool _516_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _517___v32;
            Dafny.ISequence<Dafny.Rune> _out132;
            bool _out133;
            bool _out134;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
            DCOMP.COMP.GenExpr((_511_values).Select(_512_i), selfIdent, @params, true, out _out132, out _out133, out _out134, out _out135);
            _514___v30 = _out132;
            _515___v31 = _out133;
            _516_isErased = _out134;
            _517___v32 = _out135;
            _513_allErased = (_513_allErased) && (_516_isErased);
            _512_i = (_512_i) + (BigInteger.One);
          }
          _512_i = BigInteger.Zero;
          while ((_512_i) < (new BigInteger((_511_values).Count))) {
            if ((_512_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
            }
            Dafny.ISequence<Dafny.Rune> _518_recursiveGen;
            bool _519___v33;
            bool _520_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _521_recIdents;
            Dafny.ISequence<Dafny.Rune> _out136;
            bool _out137;
            bool _out138;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out139;
            DCOMP.COMP.GenExpr((_511_values).Select(_512_i), selfIdent, @params, true, out _out136, out _out137, out _out138, out _out139);
            _518_recursiveGen = _out136;
            _519___v33 = _out137;
            _520_isErased = _out138;
            _521_recIdents = _out139;
            if ((_520_isErased) && (!(_513_allErased))) {
              _518_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _518_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _518_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _521_recIdents);
            _512_i = (_512_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = _513_allErased;
        }
      } else if (_source21.is_New) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _522___mcc_h12 = _source21.dtor_path;
        Dafny.ISequence<DAST._IExpression> _523___mcc_h13 = _source21.dtor_args;
        Dafny.ISequence<DAST._IExpression> _524_args = _523___mcc_h13;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _525_path = _522___mcc_h12;
        {
          Dafny.ISequence<Dafny.Rune> _526_path;
          Dafny.ISequence<Dafny.Rune> _out140;
          _out140 = DCOMP.COMP.GenPath(_525_path);
          _526_path = _out140;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _526_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new("));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _527_i;
          _527_i = BigInteger.Zero;
          while ((_527_i) < (new BigInteger((_524_args).Count))) {
            if ((_527_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _528_recursiveGen;
            bool _529___v34;
            bool _530_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _531_recIdents;
            Dafny.ISequence<Dafny.Rune> _out141;
            bool _out142;
            bool _out143;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
            DCOMP.COMP.GenExpr((_524_args).Select(_527_i), selfIdent, @params, true, out _out141, out _out142, out _out143, out _out144);
            _528_recursiveGen = _out141;
            _529___v34 = _out142;
            _530_isErased = _out143;
            _531_recIdents = _out144;
            if (_530_isErased) {
              _528_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _528_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _528_recursiveGen);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _531_recIdents);
            _527_i = (_527_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source21.is_NewArray) {
        Dafny.ISequence<DAST._IExpression> _532___mcc_h14 = _source21.dtor_dims;
        Dafny.ISequence<DAST._IExpression> _533_dims = _532___mcc_h14;
        {
          BigInteger _534_i;
          _534_i = (new BigInteger((_533_dims).Count)) - (BigInteger.One);
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          while ((_534_i).Sign != -1) {
            Dafny.ISequence<Dafny.Rune> _535_recursiveGen;
            bool _536___v35;
            bool _537_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _538_recIdents;
            Dafny.ISequence<Dafny.Rune> _out145;
            bool _out146;
            bool _out147;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out148;
            DCOMP.COMP.GenExpr((_533_dims).Select(_534_i), selfIdent, @params, true, out _out145, out _out146, out _out147, out _out148);
            _535_recursiveGen = _out145;
            _536___v35 = _out146;
            _537_isErased = _out147;
            _538_recIdents = _out148;
            if (!(_537_isErased)) {
              _535_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _535_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), _535_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _538_recIdents);
            _534_i = (_534_i) - (BigInteger.One);
          }
          isOwned = true;
          isErased = true;
        }
      } else if (_source21.is_DatatypeValue) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _539___mcc_h15 = _source21.dtor_path;
        Dafny.ISequence<Dafny.Rune> _540___mcc_h16 = _source21.dtor_variant;
        bool _541___mcc_h17 = _source21.dtor_isCo;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _542___mcc_h18 = _source21.dtor_contents;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _543_values = _542___mcc_h18;
        bool _544_isCo = _541___mcc_h17;
        Dafny.ISequence<Dafny.Rune> _545_variant = _540___mcc_h16;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _546_path = _539___mcc_h15;
        {
          Dafny.ISequence<Dafny.Rune> _547_path;
          Dafny.ISequence<Dafny.Rune> _out149;
          _out149 = DCOMP.COMP.GenPath(_546_path);
          _547_path = _out149;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _547_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _545_variant);
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _548_i;
          _548_i = BigInteger.Zero;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {"));
          while ((_548_i) < (new BigInteger((_543_values).Count))) {
            _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs0 = (_543_values).Select(_548_i);
            Dafny.ISequence<Dafny.Rune> _549_name = _let_tmp_rhs0.dtor__0;
            DAST._IExpression _550_value = _let_tmp_rhs0.dtor__1;
            if ((_548_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            if (_544_isCo) {
              Dafny.ISequence<Dafny.Rune> _551_recursiveGen;
              bool _552___v36;
              bool _553_isErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _554_recIdents;
              Dafny.ISequence<Dafny.Rune> _out150;
              bool _out151;
              bool _out152;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out153;
              DCOMP.COMP.GenExpr(_550_value, selfIdent, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), true, out _out150, out _out151, out _out152, out _out153);
              _551_recursiveGen = _out150;
              _552___v36 = _out151;
              _553_isErased = _out152;
              _554_recIdents = _out153;
              if (!(_553_isErased)) {
                _551_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _551_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _551_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _551_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _554_recIdents);
              Dafny.ISequence<Dafny.Rune> _555_allReadCloned;
              _555_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              while (!(_554_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                Dafny.ISequence<Dafny.Rune> _556_next;
                foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_0 in (_554_recIdents).Elements) {
                  _556_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_0;
                  if ((_554_recIdents).Contains(_556_next)) {
                    goto after__ASSIGN_SUCH_THAT_0;
                  }
                }
                throw new System.Exception("assign-such-that search produced no value (line 1185)");
              after__ASSIGN_SUCH_THAT_0:;
                _555_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_555_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), _556_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _556_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                _554_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_554_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_556_next));
              }
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _549_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n")), _555_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), _551_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
            } else {
              Dafny.ISequence<Dafny.Rune> _557_recursiveGen;
              bool _558___v37;
              bool _559_isErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _560_recIdents;
              Dafny.ISequence<Dafny.Rune> _out154;
              bool _out155;
              bool _out156;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out157;
              DCOMP.COMP.GenExpr(_550_value, selfIdent, @params, true, out _out154, out _out155, out _out156, out _out157);
              _557_recursiveGen = _out154;
              _558___v37 = _out155;
              _559_isErased = _out156;
              _560_recIdents = _out157;
              if (!(_559_isErased)) {
                _557_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _557_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _557_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _557_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _549_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _557_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _560_recIdents);
            }
            _548_i = (_548_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" })"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source21.is_Convert) {
        DAST._IExpression _561___mcc_h19 = _source21.dtor_value;
        DAST._IType _562___mcc_h20 = _source21.dtor_from;
        DAST._IType _563___mcc_h21 = _source21.dtor_typ;
        DAST._IType _564_toTpe = _563___mcc_h21;
        DAST._IType _565_fromTpe = _562___mcc_h20;
        DAST._IExpression _566_expr = _561___mcc_h19;
        {
          if (object.Equals(_565_fromTpe, _564_toTpe)) {
            Dafny.ISequence<Dafny.Rune> _567_recursiveGen;
            bool _568_recOwned;
            bool _569_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _570_recIdents;
            Dafny.ISequence<Dafny.Rune> _out158;
            bool _out159;
            bool _out160;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out161;
            DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out158, out _out159, out _out160, out _out161);
            _567_recursiveGen = _out158;
            _568_recOwned = _out159;
            _569_recErased = _out160;
            _570_recIdents = _out161;
            s = _567_recursiveGen;
            isOwned = _568_recOwned;
            isErased = _569_recErased;
            readIdents = _570_recIdents;
          } else {
            _System._ITuple2<DAST._IType, DAST._IType> _source27 = _System.Tuple2<DAST._IType, DAST._IType>.create(_565_fromTpe, _564_toTpe);
            DAST._IType _571___mcc_h283 = _source27.dtor__0;
            DAST._IType _572___mcc_h284 = _source27.dtor__1;
            DAST._IType _source28 = _571___mcc_h283;
            if (_source28.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _573___mcc_h287 = _source28.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _574___mcc_h288 = _source28.dtor_typeArgs;
              DAST._IResolvedType _575___mcc_h289 = _source28.dtor_resolved;
              DAST._IResolvedType _source29 = _575___mcc_h289;
              if (_source29.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _576___mcc_h299 = _source29.dtor_path;
                DAST._IType _source30 = _572___mcc_h284;
                if (_source30.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _577___mcc_h303 = _source30.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _578___mcc_h304 = _source30.dtor_typeArgs;
                  DAST._IResolvedType _579___mcc_h305 = _source30.dtor_resolved;
                  DAST._IResolvedType _source31 = _579___mcc_h305;
                  if (_source31.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _580___mcc_h309 = _source31.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _581_recursiveGen;
                      bool _582_recOwned;
                      bool _583_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _584_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out162;
                      bool _out163;
                      bool _out164;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out165;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out162, out _out163, out _out164, out _out165);
                      _581_recursiveGen = _out162;
                      _582_recOwned = _out163;
                      _583_recErased = _out164;
                      _584_recIdents = _out165;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _581_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _582_recOwned;
                      isErased = _583_recErased;
                      readIdents = _584_recIdents;
                    }
                  } else if (_source31.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _585___mcc_h311 = _source31.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _586_recursiveGen;
                      bool _587_recOwned;
                      bool _588_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _589_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out166;
                      bool _out167;
                      bool _out168;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out169;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out166, out _out167, out _out168, out _out169);
                      _586_recursiveGen = _out166;
                      _587_recOwned = _out167;
                      _588_recErased = _out168;
                      _589_recIdents = _out169;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _586_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _587_recOwned;
                      isErased = _588_recErased;
                      readIdents = _589_recIdents;
                    }
                  } else {
                    DAST._IType _590___mcc_h313 = _source31.dtor_Newtype_a0;
                    DAST._IType _591_b = _590___mcc_h313;
                    {
                      if (object.Equals(_565_fromTpe, _591_b)) {
                        Dafny.ISequence<Dafny.Rune> _592_recursiveGen;
                        bool _593_recOwned;
                        bool _594_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _595_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out170;
                        bool _out171;
                        bool _out172;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out173;
                        DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out170, out _out171, out _out172, out _out173);
                        _592_recursiveGen = _out170;
                        _593_recOwned = _out171;
                        _594_recErased = _out172;
                        _595_recIdents = _out173;
                        Dafny.ISequence<Dafny.Rune> _596_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out174;
                        _out174 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                        _596_rhsType = _out174;
                        Dafny.ISequence<Dafny.Rune> _597_uneraseFn;
                        _597_uneraseFn = ((_593_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _596_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _597_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _592_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _593_recOwned;
                        isErased = false;
                        readIdents = _595_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out175;
                        bool _out176;
                        bool _out177;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out178;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _591_b), _591_b, _564_toTpe), selfIdent, @params, mustOwn, out _out175, out _out176, out _out177, out _out178);
                        s = _out175;
                        isOwned = _out176;
                        isErased = _out177;
                        readIdents = _out178;
                      }
                    }
                  }
                } else if (_source30.is_Nullable) {
                  DAST._IType _598___mcc_h315 = _source30.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _599_recursiveGen;
                    bool _600_recOwned;
                    bool _601_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _602_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out179;
                    bool _out180;
                    bool _out181;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out182;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out179, out _out180, out _out181, out _out182);
                    _599_recursiveGen = _out179;
                    _600_recOwned = _out180;
                    _601_recErased = _out181;
                    _602_recIdents = _out182;
                    if (!(_600_recOwned)) {
                      _599_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_599_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _599_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _601_recErased;
                    readIdents = _602_recIdents;
                  }
                } else if (_source30.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _603___mcc_h317 = _source30.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _604_recursiveGen;
                    bool _605_recOwned;
                    bool _606_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _607_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out183;
                    bool _out184;
                    bool _out185;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out186;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out183, out _out184, out _out185, out _out186);
                    _604_recursiveGen = _out183;
                    _605_recOwned = _out184;
                    _606_recErased = _out185;
                    _607_recIdents = _out186;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _604_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _605_recOwned;
                    isErased = _606_recErased;
                    readIdents = _607_recIdents;
                  }
                } else if (_source30.is_Array) {
                  DAST._IType _608___mcc_h319 = _source30.dtor_element;
                  BigInteger _609___mcc_h320 = _source30.dtor_dims;
                  {
                    Dafny.ISequence<Dafny.Rune> _610_recursiveGen;
                    bool _611_recOwned;
                    bool _612_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _613_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out187;
                    bool _out188;
                    bool _out189;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out190;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out187, out _out188, out _out189, out _out190);
                    _610_recursiveGen = _out187;
                    _611_recOwned = _out188;
                    _612_recErased = _out189;
                    _613_recIdents = _out190;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _610_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _611_recOwned;
                    isErased = _612_recErased;
                    readIdents = _613_recIdents;
                  }
                } else if (_source30.is_Seq) {
                  DAST._IType _614___mcc_h323 = _source30.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _615_recursiveGen;
                    bool _616_recOwned;
                    bool _617_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _618_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out191;
                    bool _out192;
                    bool _out193;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out194;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out191, out _out192, out _out193, out _out194);
                    _615_recursiveGen = _out191;
                    _616_recOwned = _out192;
                    _617_recErased = _out193;
                    _618_recIdents = _out194;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _615_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _616_recOwned;
                    isErased = _617_recErased;
                    readIdents = _618_recIdents;
                  }
                } else if (_source30.is_Set) {
                  DAST._IType _619___mcc_h325 = _source30.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _620_recursiveGen;
                    bool _621_recOwned;
                    bool _622_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _623_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out195;
                    bool _out196;
                    bool _out197;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out198;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out195, out _out196, out _out197, out _out198);
                    _620_recursiveGen = _out195;
                    _621_recOwned = _out196;
                    _622_recErased = _out197;
                    _623_recIdents = _out198;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _620_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _621_recOwned;
                    isErased = _622_recErased;
                    readIdents = _623_recIdents;
                  }
                } else if (_source30.is_Multiset) {
                  DAST._IType _624___mcc_h327 = _source30.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _625_recursiveGen;
                    bool _626_recOwned;
                    bool _627_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _628_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out199;
                    bool _out200;
                    bool _out201;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out202;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out199, out _out200, out _out201, out _out202);
                    _625_recursiveGen = _out199;
                    _626_recOwned = _out200;
                    _627_recErased = _out201;
                    _628_recIdents = _out202;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _625_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _626_recOwned;
                    isErased = _627_recErased;
                    readIdents = _628_recIdents;
                  }
                } else if (_source30.is_Map) {
                  DAST._IType _629___mcc_h329 = _source30.dtor_key;
                  DAST._IType _630___mcc_h330 = _source30.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _631_recursiveGen;
                    bool _632_recOwned;
                    bool _633_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _634_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out203;
                    bool _out204;
                    bool _out205;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out206;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out203, out _out204, out _out205, out _out206);
                    _631_recursiveGen = _out203;
                    _632_recOwned = _out204;
                    _633_recErased = _out205;
                    _634_recIdents = _out206;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _631_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _632_recOwned;
                    isErased = _633_recErased;
                    readIdents = _634_recIdents;
                  }
                } else if (_source30.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _635___mcc_h333 = _source30.dtor_args;
                  DAST._IType _636___mcc_h334 = _source30.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _637_recursiveGen;
                    bool _638_recOwned;
                    bool _639_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _640_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out207;
                    bool _out208;
                    bool _out209;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out210;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out207, out _out208, out _out209, out _out210);
                    _637_recursiveGen = _out207;
                    _638_recOwned = _out208;
                    _639_recErased = _out209;
                    _640_recIdents = _out210;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _637_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _638_recOwned;
                    isErased = _639_recErased;
                    readIdents = _640_recIdents;
                  }
                } else if (_source30.is_Primitive) {
                  DAST._IPrimitive _641___mcc_h337 = _source30.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _642_recursiveGen;
                    bool _643_recOwned;
                    bool _644_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _645_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out211;
                    bool _out212;
                    bool _out213;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out214;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out211, out _out212, out _out213, out _out214);
                    _642_recursiveGen = _out211;
                    _643_recOwned = _out212;
                    _644_recErased = _out213;
                    _645_recIdents = _out214;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _642_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _643_recOwned;
                    isErased = _644_recErased;
                    readIdents = _645_recIdents;
                  }
                } else if (_source30.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _646___mcc_h339 = _source30.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _647_recursiveGen;
                    bool _648_recOwned;
                    bool _649_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _650_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out215;
                    bool _out216;
                    bool _out217;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out218;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out215, out _out216, out _out217, out _out218);
                    _647_recursiveGen = _out215;
                    _648_recOwned = _out216;
                    _649_recErased = _out217;
                    _650_recIdents = _out218;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _647_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _648_recOwned;
                    isErased = _649_recErased;
                    readIdents = _650_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _651___mcc_h341 = _source30.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _652_recursiveGen;
                    bool _653_recOwned;
                    bool _654_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _655_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out219;
                    bool _out220;
                    bool _out221;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out222;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out219, out _out220, out _out221, out _out222);
                    _652_recursiveGen = _out219;
                    _653_recOwned = _out220;
                    _654_recErased = _out221;
                    _655_recIdents = _out222;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _652_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _653_recOwned;
                    isErased = _654_recErased;
                    readIdents = _655_recIdents;
                  }
                }
              } else if (_source29.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _656___mcc_h343 = _source29.dtor_path;
                DAST._IType _source32 = _572___mcc_h284;
                if (_source32.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _657___mcc_h347 = _source32.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _658___mcc_h348 = _source32.dtor_typeArgs;
                  DAST._IResolvedType _659___mcc_h349 = _source32.dtor_resolved;
                  DAST._IResolvedType _source33 = _659___mcc_h349;
                  if (_source33.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _660___mcc_h353 = _source33.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _661_recursiveGen;
                      bool _662_recOwned;
                      bool _663_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _664_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out223;
                      bool _out224;
                      bool _out225;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out226;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out223, out _out224, out _out225, out _out226);
                      _661_recursiveGen = _out223;
                      _662_recOwned = _out224;
                      _663_recErased = _out225;
                      _664_recIdents = _out226;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _661_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _662_recOwned;
                      isErased = _663_recErased;
                      readIdents = _664_recIdents;
                    }
                  } else if (_source33.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _665___mcc_h355 = _source33.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _666_recursiveGen;
                      bool _667_recOwned;
                      bool _668_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _669_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out227;
                      bool _out228;
                      bool _out229;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out230;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out227, out _out228, out _out229, out _out230);
                      _666_recursiveGen = _out227;
                      _667_recOwned = _out228;
                      _668_recErased = _out229;
                      _669_recIdents = _out230;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _666_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _667_recOwned;
                      isErased = _668_recErased;
                      readIdents = _669_recIdents;
                    }
                  } else {
                    DAST._IType _670___mcc_h357 = _source33.dtor_Newtype_a0;
                    DAST._IType _671_b = _670___mcc_h357;
                    {
                      if (object.Equals(_565_fromTpe, _671_b)) {
                        Dafny.ISequence<Dafny.Rune> _672_recursiveGen;
                        bool _673_recOwned;
                        bool _674_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _675_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out231;
                        bool _out232;
                        bool _out233;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out234;
                        DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out231, out _out232, out _out233, out _out234);
                        _672_recursiveGen = _out231;
                        _673_recOwned = _out232;
                        _674_recErased = _out233;
                        _675_recIdents = _out234;
                        Dafny.ISequence<Dafny.Rune> _676_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out235;
                        _out235 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                        _676_rhsType = _out235;
                        Dafny.ISequence<Dafny.Rune> _677_uneraseFn;
                        _677_uneraseFn = ((_673_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _676_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _677_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _672_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _673_recOwned;
                        isErased = false;
                        readIdents = _675_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out236;
                        bool _out237;
                        bool _out238;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out239;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _671_b), _671_b, _564_toTpe), selfIdent, @params, mustOwn, out _out236, out _out237, out _out238, out _out239);
                        s = _out236;
                        isOwned = _out237;
                        isErased = _out238;
                        readIdents = _out239;
                      }
                    }
                  }
                } else if (_source32.is_Nullable) {
                  DAST._IType _678___mcc_h359 = _source32.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _679_recursiveGen;
                    bool _680_recOwned;
                    bool _681_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _682_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out240;
                    bool _out241;
                    bool _out242;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out243;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out240, out _out241, out _out242, out _out243);
                    _679_recursiveGen = _out240;
                    _680_recOwned = _out241;
                    _681_recErased = _out242;
                    _682_recIdents = _out243;
                    if (!(_680_recOwned)) {
                      _679_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_679_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _679_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _681_recErased;
                    readIdents = _682_recIdents;
                  }
                } else if (_source32.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _683___mcc_h361 = _source32.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _684_recursiveGen;
                    bool _685_recOwned;
                    bool _686_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _687_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out244;
                    bool _out245;
                    bool _out246;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out247;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out244, out _out245, out _out246, out _out247);
                    _684_recursiveGen = _out244;
                    _685_recOwned = _out245;
                    _686_recErased = _out246;
                    _687_recIdents = _out247;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _684_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _685_recOwned;
                    isErased = _686_recErased;
                    readIdents = _687_recIdents;
                  }
                } else if (_source32.is_Array) {
                  DAST._IType _688___mcc_h363 = _source32.dtor_element;
                  BigInteger _689___mcc_h364 = _source32.dtor_dims;
                  {
                    Dafny.ISequence<Dafny.Rune> _690_recursiveGen;
                    bool _691_recOwned;
                    bool _692_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _693_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out248;
                    bool _out249;
                    bool _out250;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out251;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out248, out _out249, out _out250, out _out251);
                    _690_recursiveGen = _out248;
                    _691_recOwned = _out249;
                    _692_recErased = _out250;
                    _693_recIdents = _out251;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _690_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _691_recOwned;
                    isErased = _692_recErased;
                    readIdents = _693_recIdents;
                  }
                } else if (_source32.is_Seq) {
                  DAST._IType _694___mcc_h367 = _source32.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _695_recursiveGen;
                    bool _696_recOwned;
                    bool _697_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _698_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out252;
                    bool _out253;
                    bool _out254;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out255;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out252, out _out253, out _out254, out _out255);
                    _695_recursiveGen = _out252;
                    _696_recOwned = _out253;
                    _697_recErased = _out254;
                    _698_recIdents = _out255;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _695_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _696_recOwned;
                    isErased = _697_recErased;
                    readIdents = _698_recIdents;
                  }
                } else if (_source32.is_Set) {
                  DAST._IType _699___mcc_h369 = _source32.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _700_recursiveGen;
                    bool _701_recOwned;
                    bool _702_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _703_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out256;
                    bool _out257;
                    bool _out258;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out259;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out256, out _out257, out _out258, out _out259);
                    _700_recursiveGen = _out256;
                    _701_recOwned = _out257;
                    _702_recErased = _out258;
                    _703_recIdents = _out259;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _700_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _701_recOwned;
                    isErased = _702_recErased;
                    readIdents = _703_recIdents;
                  }
                } else if (_source32.is_Multiset) {
                  DAST._IType _704___mcc_h371 = _source32.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _705_recursiveGen;
                    bool _706_recOwned;
                    bool _707_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _708_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out260;
                    bool _out261;
                    bool _out262;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out263;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out260, out _out261, out _out262, out _out263);
                    _705_recursiveGen = _out260;
                    _706_recOwned = _out261;
                    _707_recErased = _out262;
                    _708_recIdents = _out263;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _705_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _706_recOwned;
                    isErased = _707_recErased;
                    readIdents = _708_recIdents;
                  }
                } else if (_source32.is_Map) {
                  DAST._IType _709___mcc_h373 = _source32.dtor_key;
                  DAST._IType _710___mcc_h374 = _source32.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _711_recursiveGen;
                    bool _712_recOwned;
                    bool _713_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _714_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out264;
                    bool _out265;
                    bool _out266;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out267;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out264, out _out265, out _out266, out _out267);
                    _711_recursiveGen = _out264;
                    _712_recOwned = _out265;
                    _713_recErased = _out266;
                    _714_recIdents = _out267;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _711_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _712_recOwned;
                    isErased = _713_recErased;
                    readIdents = _714_recIdents;
                  }
                } else if (_source32.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _715___mcc_h377 = _source32.dtor_args;
                  DAST._IType _716___mcc_h378 = _source32.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _717_recursiveGen;
                    bool _718_recOwned;
                    bool _719_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _720_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out268;
                    bool _out269;
                    bool _out270;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out271;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out268, out _out269, out _out270, out _out271);
                    _717_recursiveGen = _out268;
                    _718_recOwned = _out269;
                    _719_recErased = _out270;
                    _720_recIdents = _out271;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _717_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _718_recOwned;
                    isErased = _719_recErased;
                    readIdents = _720_recIdents;
                  }
                } else if (_source32.is_Primitive) {
                  DAST._IPrimitive _721___mcc_h381 = _source32.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _722_recursiveGen;
                    bool _723_recOwned;
                    bool _724_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _725_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out272;
                    bool _out273;
                    bool _out274;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out275;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out272, out _out273, out _out274, out _out275);
                    _722_recursiveGen = _out272;
                    _723_recOwned = _out273;
                    _724_recErased = _out274;
                    _725_recIdents = _out275;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _722_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _723_recOwned;
                    isErased = _724_recErased;
                    readIdents = _725_recIdents;
                  }
                } else if (_source32.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _726___mcc_h383 = _source32.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _727_recursiveGen;
                    bool _728_recOwned;
                    bool _729_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _730_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out276;
                    bool _out277;
                    bool _out278;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out279;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out276, out _out277, out _out278, out _out279);
                    _727_recursiveGen = _out276;
                    _728_recOwned = _out277;
                    _729_recErased = _out278;
                    _730_recIdents = _out279;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _727_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _728_recOwned;
                    isErased = _729_recErased;
                    readIdents = _730_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _731___mcc_h385 = _source32.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _732_recursiveGen;
                    bool _733_recOwned;
                    bool _734_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _735_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out280;
                    bool _out281;
                    bool _out282;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out283;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out280, out _out281, out _out282, out _out283);
                    _732_recursiveGen = _out280;
                    _733_recOwned = _out281;
                    _734_recErased = _out282;
                    _735_recIdents = _out283;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _732_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _733_recOwned;
                    isErased = _734_recErased;
                    readIdents = _735_recIdents;
                  }
                }
              } else {
                DAST._IType _736___mcc_h387 = _source29.dtor_Newtype_a0;
                DAST._IType _source34 = _572___mcc_h284;
                if (_source34.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _737___mcc_h391 = _source34.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _738___mcc_h392 = _source34.dtor_typeArgs;
                  DAST._IResolvedType _739___mcc_h393 = _source34.dtor_resolved;
                  DAST._IResolvedType _source35 = _739___mcc_h393;
                  if (_source35.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _740___mcc_h400 = _source35.dtor_path;
                    DAST._IType _741_b = _736___mcc_h387;
                    {
                      if (object.Equals(_741_b, _564_toTpe)) {
                        Dafny.ISequence<Dafny.Rune> _742_recursiveGen;
                        bool _743_recOwned;
                        bool _744_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _745_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out284;
                        bool _out285;
                        bool _out286;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out287;
                        DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out284, out _out285, out _out286, out _out287);
                        _742_recursiveGen = _out284;
                        _743_recOwned = _out285;
                        _744_recErased = _out286;
                        _745_recIdents = _out287;
                        Dafny.ISequence<Dafny.Rune> _746_uneraseFn;
                        _746_uneraseFn = ((_743_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _746_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _742_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _743_recOwned;
                        isErased = true;
                        readIdents = _745_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out288;
                        bool _out289;
                        bool _out290;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out291;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _741_b), _741_b, _564_toTpe), selfIdent, @params, mustOwn, out _out288, out _out289, out _out290, out _out291);
                        s = _out288;
                        isOwned = _out289;
                        isErased = _out290;
                        readIdents = _out291;
                      }
                    }
                  } else if (_source35.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _747___mcc_h403 = _source35.dtor_path;
                    DAST._IType _748_b = _736___mcc_h387;
                    {
                      if (object.Equals(_748_b, _564_toTpe)) {
                        Dafny.ISequence<Dafny.Rune> _749_recursiveGen;
                        bool _750_recOwned;
                        bool _751_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _752_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out292;
                        bool _out293;
                        bool _out294;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out295;
                        DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out292, out _out293, out _out294, out _out295);
                        _749_recursiveGen = _out292;
                        _750_recOwned = _out293;
                        _751_recErased = _out294;
                        _752_recIdents = _out295;
                        Dafny.ISequence<Dafny.Rune> _753_uneraseFn;
                        _753_uneraseFn = ((_750_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _753_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _749_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _750_recOwned;
                        isErased = true;
                        readIdents = _752_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out296;
                        bool _out297;
                        bool _out298;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out299;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _748_b), _748_b, _564_toTpe), selfIdent, @params, mustOwn, out _out296, out _out297, out _out298, out _out299);
                        s = _out296;
                        isOwned = _out297;
                        isErased = _out298;
                        readIdents = _out299;
                      }
                    }
                  } else {
                    DAST._IType _754___mcc_h406 = _source35.dtor_Newtype_a0;
                    DAST._IType _755_b = _754___mcc_h406;
                    {
                      if (object.Equals(_565_fromTpe, _755_b)) {
                        Dafny.ISequence<Dafny.Rune> _756_recursiveGen;
                        bool _757_recOwned;
                        bool _758_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _759_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out300;
                        bool _out301;
                        bool _out302;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out303;
                        DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out300, out _out301, out _out302, out _out303);
                        _756_recursiveGen = _out300;
                        _757_recOwned = _out301;
                        _758_recErased = _out302;
                        _759_recIdents = _out303;
                        Dafny.ISequence<Dafny.Rune> _760_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out304;
                        _out304 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                        _760_rhsType = _out304;
                        Dafny.ISequence<Dafny.Rune> _761_uneraseFn;
                        _761_uneraseFn = ((_757_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _760_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _761_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _756_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _757_recOwned;
                        isErased = false;
                        readIdents = _759_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out305;
                        bool _out306;
                        bool _out307;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out308;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _755_b), _755_b, _564_toTpe), selfIdent, @params, mustOwn, out _out305, out _out306, out _out307, out _out308);
                        s = _out305;
                        isOwned = _out306;
                        isErased = _out307;
                        readIdents = _out308;
                      }
                    }
                  }
                } else if (_source34.is_Nullable) {
                  DAST._IType _762___mcc_h409 = _source34.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _763_recursiveGen;
                    bool _764_recOwned;
                    bool _765_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _766_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out309;
                    bool _out310;
                    bool _out311;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out312;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out309, out _out310, out _out311, out _out312);
                    _763_recursiveGen = _out309;
                    _764_recOwned = _out310;
                    _765_recErased = _out311;
                    _766_recIdents = _out312;
                    if (!(_764_recOwned)) {
                      _763_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_763_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _763_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _765_recErased;
                    readIdents = _766_recIdents;
                  }
                } else if (_source34.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _767___mcc_h412 = _source34.dtor_Tuple_a0;
                  DAST._IType _768_b = _736___mcc_h387;
                  {
                    if (object.Equals(_768_b, _564_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _769_recursiveGen;
                      bool _770_recOwned;
                      bool _771_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _772_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out313;
                      bool _out314;
                      bool _out315;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out316;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out313, out _out314, out _out315, out _out316);
                      _769_recursiveGen = _out313;
                      _770_recOwned = _out314;
                      _771_recErased = _out315;
                      _772_recIdents = _out316;
                      Dafny.ISequence<Dafny.Rune> _773_uneraseFn;
                      _773_uneraseFn = ((_770_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _773_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _769_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _770_recOwned;
                      isErased = true;
                      readIdents = _772_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out317;
                      bool _out318;
                      bool _out319;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out320;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _768_b), _768_b, _564_toTpe), selfIdent, @params, mustOwn, out _out317, out _out318, out _out319, out _out320);
                      s = _out317;
                      isOwned = _out318;
                      isErased = _out319;
                      readIdents = _out320;
                    }
                  }
                } else if (_source34.is_Array) {
                  DAST._IType _774___mcc_h415 = _source34.dtor_element;
                  BigInteger _775___mcc_h416 = _source34.dtor_dims;
                  DAST._IType _776_b = _736___mcc_h387;
                  {
                    if (object.Equals(_776_b, _564_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _777_recursiveGen;
                      bool _778_recOwned;
                      bool _779_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _780_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out321;
                      bool _out322;
                      bool _out323;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out324;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out321, out _out322, out _out323, out _out324);
                      _777_recursiveGen = _out321;
                      _778_recOwned = _out322;
                      _779_recErased = _out323;
                      _780_recIdents = _out324;
                      Dafny.ISequence<Dafny.Rune> _781_uneraseFn;
                      _781_uneraseFn = ((_778_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _781_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _777_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _778_recOwned;
                      isErased = true;
                      readIdents = _780_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out325;
                      bool _out326;
                      bool _out327;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out328;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _776_b), _776_b, _564_toTpe), selfIdent, @params, mustOwn, out _out325, out _out326, out _out327, out _out328);
                      s = _out325;
                      isOwned = _out326;
                      isErased = _out327;
                      readIdents = _out328;
                    }
                  }
                } else if (_source34.is_Seq) {
                  DAST._IType _782___mcc_h421 = _source34.dtor_element;
                  DAST._IType _783_b = _736___mcc_h387;
                  {
                    if (object.Equals(_783_b, _564_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _784_recursiveGen;
                      bool _785_recOwned;
                      bool _786_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _787_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out329;
                      bool _out330;
                      bool _out331;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out332;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out329, out _out330, out _out331, out _out332);
                      _784_recursiveGen = _out329;
                      _785_recOwned = _out330;
                      _786_recErased = _out331;
                      _787_recIdents = _out332;
                      Dafny.ISequence<Dafny.Rune> _788_uneraseFn;
                      _788_uneraseFn = ((_785_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _788_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _784_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _785_recOwned;
                      isErased = true;
                      readIdents = _787_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out333;
                      bool _out334;
                      bool _out335;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out336;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _783_b), _783_b, _564_toTpe), selfIdent, @params, mustOwn, out _out333, out _out334, out _out335, out _out336);
                      s = _out333;
                      isOwned = _out334;
                      isErased = _out335;
                      readIdents = _out336;
                    }
                  }
                } else if (_source34.is_Set) {
                  DAST._IType _789___mcc_h424 = _source34.dtor_element;
                  DAST._IType _790_b = _736___mcc_h387;
                  {
                    if (object.Equals(_790_b, _564_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _791_recursiveGen;
                      bool _792_recOwned;
                      bool _793_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _794_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out337;
                      bool _out338;
                      bool _out339;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out340;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out337, out _out338, out _out339, out _out340);
                      _791_recursiveGen = _out337;
                      _792_recOwned = _out338;
                      _793_recErased = _out339;
                      _794_recIdents = _out340;
                      Dafny.ISequence<Dafny.Rune> _795_uneraseFn;
                      _795_uneraseFn = ((_792_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _795_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _791_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _792_recOwned;
                      isErased = true;
                      readIdents = _794_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out341;
                      bool _out342;
                      bool _out343;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out344;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _790_b), _790_b, _564_toTpe), selfIdent, @params, mustOwn, out _out341, out _out342, out _out343, out _out344);
                      s = _out341;
                      isOwned = _out342;
                      isErased = _out343;
                      readIdents = _out344;
                    }
                  }
                } else if (_source34.is_Multiset) {
                  DAST._IType _796___mcc_h427 = _source34.dtor_element;
                  DAST._IType _797_b = _736___mcc_h387;
                  {
                    if (object.Equals(_797_b, _564_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _798_recursiveGen;
                      bool _799_recOwned;
                      bool _800_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _801_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out345;
                      bool _out346;
                      bool _out347;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out348;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out345, out _out346, out _out347, out _out348);
                      _798_recursiveGen = _out345;
                      _799_recOwned = _out346;
                      _800_recErased = _out347;
                      _801_recIdents = _out348;
                      Dafny.ISequence<Dafny.Rune> _802_uneraseFn;
                      _802_uneraseFn = ((_799_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _802_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _798_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _799_recOwned;
                      isErased = true;
                      readIdents = _801_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out349;
                      bool _out350;
                      bool _out351;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out352;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _797_b), _797_b, _564_toTpe), selfIdent, @params, mustOwn, out _out349, out _out350, out _out351, out _out352);
                      s = _out349;
                      isOwned = _out350;
                      isErased = _out351;
                      readIdents = _out352;
                    }
                  }
                } else if (_source34.is_Map) {
                  DAST._IType _803___mcc_h430 = _source34.dtor_key;
                  DAST._IType _804___mcc_h431 = _source34.dtor_value;
                  DAST._IType _805_b = _736___mcc_h387;
                  {
                    if (object.Equals(_805_b, _564_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _806_recursiveGen;
                      bool _807_recOwned;
                      bool _808_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _809_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out353;
                      bool _out354;
                      bool _out355;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out356;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out353, out _out354, out _out355, out _out356);
                      _806_recursiveGen = _out353;
                      _807_recOwned = _out354;
                      _808_recErased = _out355;
                      _809_recIdents = _out356;
                      Dafny.ISequence<Dafny.Rune> _810_uneraseFn;
                      _810_uneraseFn = ((_807_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _810_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _806_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _807_recOwned;
                      isErased = true;
                      readIdents = _809_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out357;
                      bool _out358;
                      bool _out359;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out360;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _805_b), _805_b, _564_toTpe), selfIdent, @params, mustOwn, out _out357, out _out358, out _out359, out _out360);
                      s = _out357;
                      isOwned = _out358;
                      isErased = _out359;
                      readIdents = _out360;
                    }
                  }
                } else if (_source34.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _811___mcc_h436 = _source34.dtor_args;
                  DAST._IType _812___mcc_h437 = _source34.dtor_result;
                  DAST._IType _813_b = _736___mcc_h387;
                  {
                    if (object.Equals(_813_b, _564_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _814_recursiveGen;
                      bool _815_recOwned;
                      bool _816_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _817_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out361;
                      bool _out362;
                      bool _out363;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out364;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out361, out _out362, out _out363, out _out364);
                      _814_recursiveGen = _out361;
                      _815_recOwned = _out362;
                      _816_recErased = _out363;
                      _817_recIdents = _out364;
                      Dafny.ISequence<Dafny.Rune> _818_uneraseFn;
                      _818_uneraseFn = ((_815_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _818_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _814_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _815_recOwned;
                      isErased = true;
                      readIdents = _817_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out365;
                      bool _out366;
                      bool _out367;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out368;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _813_b), _813_b, _564_toTpe), selfIdent, @params, mustOwn, out _out365, out _out366, out _out367, out _out368);
                      s = _out365;
                      isOwned = _out366;
                      isErased = _out367;
                      readIdents = _out368;
                    }
                  }
                } else if (_source34.is_Primitive) {
                  DAST._IPrimitive _819___mcc_h442 = _source34.dtor_Primitive_a0;
                  DAST._IType _820_b = _736___mcc_h387;
                  {
                    if (object.Equals(_820_b, _564_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _821_recursiveGen;
                      bool _822_recOwned;
                      bool _823_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _824_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out369;
                      bool _out370;
                      bool _out371;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out372;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out369, out _out370, out _out371, out _out372);
                      _821_recursiveGen = _out369;
                      _822_recOwned = _out370;
                      _823_recErased = _out371;
                      _824_recIdents = _out372;
                      Dafny.ISequence<Dafny.Rune> _825_uneraseFn;
                      _825_uneraseFn = ((_822_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _825_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _821_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _822_recOwned;
                      isErased = true;
                      readIdents = _824_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out373;
                      bool _out374;
                      bool _out375;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out376;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _820_b), _820_b, _564_toTpe), selfIdent, @params, mustOwn, out _out373, out _out374, out _out375, out _out376);
                      s = _out373;
                      isOwned = _out374;
                      isErased = _out375;
                      readIdents = _out376;
                    }
                  }
                } else if (_source34.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _826___mcc_h445 = _source34.dtor_Passthrough_a0;
                  DAST._IType _827_b = _736___mcc_h387;
                  {
                    if (object.Equals(_827_b, _564_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _828_recursiveGen;
                      bool _829_recOwned;
                      bool _830_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _831_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out377;
                      bool _out378;
                      bool _out379;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out380;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out377, out _out378, out _out379, out _out380);
                      _828_recursiveGen = _out377;
                      _829_recOwned = _out378;
                      _830_recErased = _out379;
                      _831_recIdents = _out380;
                      Dafny.ISequence<Dafny.Rune> _832_uneraseFn;
                      _832_uneraseFn = ((_829_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _832_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _828_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _829_recOwned;
                      isErased = true;
                      readIdents = _831_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out381;
                      bool _out382;
                      bool _out383;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out384;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _827_b), _827_b, _564_toTpe), selfIdent, @params, mustOwn, out _out381, out _out382, out _out383, out _out384);
                      s = _out381;
                      isOwned = _out382;
                      isErased = _out383;
                      readIdents = _out384;
                    }
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _833___mcc_h448 = _source34.dtor_TypeArg_a0;
                  DAST._IType _834_b = _736___mcc_h387;
                  {
                    if (object.Equals(_834_b, _564_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _835_recursiveGen;
                      bool _836_recOwned;
                      bool _837_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _838_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out385;
                      bool _out386;
                      bool _out387;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out388;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out385, out _out386, out _out387, out _out388);
                      _835_recursiveGen = _out385;
                      _836_recOwned = _out386;
                      _837_recErased = _out387;
                      _838_recIdents = _out388;
                      Dafny.ISequence<Dafny.Rune> _839_uneraseFn;
                      _839_uneraseFn = ((_836_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _839_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _835_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _836_recOwned;
                      isErased = true;
                      readIdents = _838_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out389;
                      bool _out390;
                      bool _out391;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out392;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _834_b), _834_b, _564_toTpe), selfIdent, @params, mustOwn, out _out389, out _out390, out _out391, out _out392);
                      s = _out389;
                      isOwned = _out390;
                      isErased = _out391;
                      readIdents = _out392;
                    }
                  }
                }
              }
            } else if (_source28.is_Nullable) {
              DAST._IType _840___mcc_h451 = _source28.dtor_Nullable_a0;
              DAST._IType _source36 = _572___mcc_h284;
              if (_source36.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _841___mcc_h455 = _source36.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _842___mcc_h456 = _source36.dtor_typeArgs;
                DAST._IResolvedType _843___mcc_h457 = _source36.dtor_resolved;
                DAST._IResolvedType _source37 = _843___mcc_h457;
                if (_source37.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _844___mcc_h464 = _source37.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _845_recursiveGen;
                    bool _846_recOwned;
                    bool _847_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _848_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out393;
                    bool _out394;
                    bool _out395;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out396;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out393, out _out394, out _out395, out _out396);
                    _845_recursiveGen = _out393;
                    _846_recOwned = _out394;
                    _847_recErased = _out395;
                    _848_recIdents = _out396;
                    if (!(_846_recOwned)) {
                      _845_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_845_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(_845_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                    isOwned = _846_recOwned;
                    isErased = _847_recErased;
                    readIdents = _848_recIdents;
                  }
                } else if (_source37.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _849___mcc_h467 = _source37.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _850_recursiveGen;
                    bool _851_recOwned;
                    bool _852_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _853_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out397;
                    bool _out398;
                    bool _out399;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out400;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out397, out _out398, out _out399, out _out400);
                    _850_recursiveGen = _out397;
                    _851_recOwned = _out398;
                    _852_recErased = _out399;
                    _853_recIdents = _out400;
                    if (!(_851_recOwned)) {
                      _850_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_850_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(_850_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                    isOwned = _851_recOwned;
                    isErased = _852_recErased;
                    readIdents = _853_recIdents;
                  }
                } else {
                  DAST._IType _854___mcc_h470 = _source37.dtor_Newtype_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _855_recursiveGen;
                    bool _856_recOwned;
                    bool _857_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _858_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out401;
                    bool _out402;
                    bool _out403;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out404;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out401, out _out402, out _out403, out _out404);
                    _855_recursiveGen = _out401;
                    _856_recOwned = _out402;
                    _857_recErased = _out403;
                    _858_recIdents = _out404;
                    if (!(_856_recOwned)) {
                      _855_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_855_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(_855_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                    isOwned = _856_recOwned;
                    isErased = _857_recErased;
                    readIdents = _858_recIdents;
                  }
                }
              } else if (_source36.is_Nullable) {
                DAST._IType _859___mcc_h473 = _source36.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _860_recursiveGen;
                  bool _861_recOwned;
                  bool _862_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _863_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out405;
                  bool _out406;
                  bool _out407;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out408;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out405, out _out406, out _out407, out _out408);
                  _860_recursiveGen = _out405;
                  _861_recOwned = _out406;
                  _862_recErased = _out407;
                  _863_recIdents = _out408;
                  if (!(_861_recOwned)) {
                    _860_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_860_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_860_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _861_recOwned;
                  isErased = _862_recErased;
                  readIdents = _863_recIdents;
                }
              } else if (_source36.is_Tuple) {
                Dafny.ISequence<DAST._IType> _864___mcc_h476 = _source36.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _865_recursiveGen;
                  bool _866_recOwned;
                  bool _867_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _868_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out409;
                  bool _out410;
                  bool _out411;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out412;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out409, out _out410, out _out411, out _out412);
                  _865_recursiveGen = _out409;
                  _866_recOwned = _out410;
                  _867_recErased = _out411;
                  _868_recIdents = _out412;
                  if (!(_866_recOwned)) {
                    _865_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_865_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_865_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _866_recOwned;
                  isErased = _867_recErased;
                  readIdents = _868_recIdents;
                }
              } else if (_source36.is_Array) {
                DAST._IType _869___mcc_h479 = _source36.dtor_element;
                BigInteger _870___mcc_h480 = _source36.dtor_dims;
                {
                  Dafny.ISequence<Dafny.Rune> _871_recursiveGen;
                  bool _872_recOwned;
                  bool _873_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _874_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out413;
                  bool _out414;
                  bool _out415;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out416;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out413, out _out414, out _out415, out _out416);
                  _871_recursiveGen = _out413;
                  _872_recOwned = _out414;
                  _873_recErased = _out415;
                  _874_recIdents = _out416;
                  if (!(_872_recOwned)) {
                    _871_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_871_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_871_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _872_recOwned;
                  isErased = _873_recErased;
                  readIdents = _874_recIdents;
                }
              } else if (_source36.is_Seq) {
                DAST._IType _875___mcc_h485 = _source36.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _876_recursiveGen;
                  bool _877_recOwned;
                  bool _878_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _879_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out417;
                  bool _out418;
                  bool _out419;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out420;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out417, out _out418, out _out419, out _out420);
                  _876_recursiveGen = _out417;
                  _877_recOwned = _out418;
                  _878_recErased = _out419;
                  _879_recIdents = _out420;
                  if (!(_877_recOwned)) {
                    _876_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_876_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_876_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _877_recOwned;
                  isErased = _878_recErased;
                  readIdents = _879_recIdents;
                }
              } else if (_source36.is_Set) {
                DAST._IType _880___mcc_h488 = _source36.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _881_recursiveGen;
                  bool _882_recOwned;
                  bool _883_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _884_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out421;
                  bool _out422;
                  bool _out423;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out424;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out421, out _out422, out _out423, out _out424);
                  _881_recursiveGen = _out421;
                  _882_recOwned = _out422;
                  _883_recErased = _out423;
                  _884_recIdents = _out424;
                  if (!(_882_recOwned)) {
                    _881_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_881_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_881_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _882_recOwned;
                  isErased = _883_recErased;
                  readIdents = _884_recIdents;
                }
              } else if (_source36.is_Multiset) {
                DAST._IType _885___mcc_h491 = _source36.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _886_recursiveGen;
                  bool _887_recOwned;
                  bool _888_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _889_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out425;
                  bool _out426;
                  bool _out427;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out428;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out425, out _out426, out _out427, out _out428);
                  _886_recursiveGen = _out425;
                  _887_recOwned = _out426;
                  _888_recErased = _out427;
                  _889_recIdents = _out428;
                  if (!(_887_recOwned)) {
                    _886_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_886_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_886_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _887_recOwned;
                  isErased = _888_recErased;
                  readIdents = _889_recIdents;
                }
              } else if (_source36.is_Map) {
                DAST._IType _890___mcc_h494 = _source36.dtor_key;
                DAST._IType _891___mcc_h495 = _source36.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _892_recursiveGen;
                  bool _893_recOwned;
                  bool _894_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _895_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out429;
                  bool _out430;
                  bool _out431;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out432;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out429, out _out430, out _out431, out _out432);
                  _892_recursiveGen = _out429;
                  _893_recOwned = _out430;
                  _894_recErased = _out431;
                  _895_recIdents = _out432;
                  if (!(_893_recOwned)) {
                    _892_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_892_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_892_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _893_recOwned;
                  isErased = _894_recErased;
                  readIdents = _895_recIdents;
                }
              } else if (_source36.is_Arrow) {
                Dafny.ISequence<DAST._IType> _896___mcc_h500 = _source36.dtor_args;
                DAST._IType _897___mcc_h501 = _source36.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _898_recursiveGen;
                  bool _899_recOwned;
                  bool _900_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _901_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out433;
                  bool _out434;
                  bool _out435;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out436;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out433, out _out434, out _out435, out _out436);
                  _898_recursiveGen = _out433;
                  _899_recOwned = _out434;
                  _900_recErased = _out435;
                  _901_recIdents = _out436;
                  if (!(_899_recOwned)) {
                    _898_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_898_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_898_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _899_recOwned;
                  isErased = _900_recErased;
                  readIdents = _901_recIdents;
                }
              } else if (_source36.is_Primitive) {
                DAST._IPrimitive _902___mcc_h506 = _source36.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _903_recursiveGen;
                  bool _904_recOwned;
                  bool _905_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _906_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out437;
                  bool _out438;
                  bool _out439;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out440;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out437, out _out438, out _out439, out _out440);
                  _903_recursiveGen = _out437;
                  _904_recOwned = _out438;
                  _905_recErased = _out439;
                  _906_recIdents = _out440;
                  if (!(_904_recOwned)) {
                    _903_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_903_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_903_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _904_recOwned;
                  isErased = _905_recErased;
                  readIdents = _906_recIdents;
                }
              } else if (_source36.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _907___mcc_h509 = _source36.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _908_recursiveGen;
                  bool _909_recOwned;
                  bool _910_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _911_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out441;
                  bool _out442;
                  bool _out443;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out444;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out441, out _out442, out _out443, out _out444);
                  _908_recursiveGen = _out441;
                  _909_recOwned = _out442;
                  _910_recErased = _out443;
                  _911_recIdents = _out444;
                  if (!(_909_recOwned)) {
                    _908_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_908_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_908_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _909_recOwned;
                  isErased = _910_recErased;
                  readIdents = _911_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _912___mcc_h512 = _source36.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _913_recursiveGen;
                  bool _914_recOwned;
                  bool _915_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _916_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out445;
                  bool _out446;
                  bool _out447;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out448;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out445, out _out446, out _out447, out _out448);
                  _913_recursiveGen = _out445;
                  _914_recOwned = _out446;
                  _915_recErased = _out447;
                  _916_recIdents = _out448;
                  if (!(_914_recOwned)) {
                    _913_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_913_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_913_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _914_recOwned;
                  isErased = _915_recErased;
                  readIdents = _916_recIdents;
                }
              }
            } else if (_source28.is_Tuple) {
              Dafny.ISequence<DAST._IType> _917___mcc_h515 = _source28.dtor_Tuple_a0;
              DAST._IType _source38 = _572___mcc_h284;
              if (_source38.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _918___mcc_h519 = _source38.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _919___mcc_h520 = _source38.dtor_typeArgs;
                DAST._IResolvedType _920___mcc_h521 = _source38.dtor_resolved;
                DAST._IResolvedType _source39 = _920___mcc_h521;
                if (_source39.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _921___mcc_h525 = _source39.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _922_recursiveGen;
                    bool _923_recOwned;
                    bool _924_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _925_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out449;
                    bool _out450;
                    bool _out451;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out452;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out449, out _out450, out _out451, out _out452);
                    _922_recursiveGen = _out449;
                    _923_recOwned = _out450;
                    _924_recErased = _out451;
                    _925_recIdents = _out452;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _922_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _923_recOwned;
                    isErased = _924_recErased;
                    readIdents = _925_recIdents;
                  }
                } else if (_source39.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _926___mcc_h527 = _source39.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _927_recursiveGen;
                    bool _928_recOwned;
                    bool _929_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _930_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out453;
                    bool _out454;
                    bool _out455;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out456;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out453, out _out454, out _out455, out _out456);
                    _927_recursiveGen = _out453;
                    _928_recOwned = _out454;
                    _929_recErased = _out455;
                    _930_recIdents = _out456;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _927_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _928_recOwned;
                    isErased = _929_recErased;
                    readIdents = _930_recIdents;
                  }
                } else {
                  DAST._IType _931___mcc_h529 = _source39.dtor_Newtype_a0;
                  DAST._IType _932_b = _931___mcc_h529;
                  {
                    if (object.Equals(_565_fromTpe, _932_b)) {
                      Dafny.ISequence<Dafny.Rune> _933_recursiveGen;
                      bool _934_recOwned;
                      bool _935_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _936_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out457;
                      bool _out458;
                      bool _out459;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out460;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out457, out _out458, out _out459, out _out460);
                      _933_recursiveGen = _out457;
                      _934_recOwned = _out458;
                      _935_recErased = _out459;
                      _936_recIdents = _out460;
                      Dafny.ISequence<Dafny.Rune> _937_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out461;
                      _out461 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                      _937_rhsType = _out461;
                      Dafny.ISequence<Dafny.Rune> _938_uneraseFn;
                      _938_uneraseFn = ((_934_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _937_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _938_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _933_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _934_recOwned;
                      isErased = false;
                      readIdents = _936_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out462;
                      bool _out463;
                      bool _out464;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out465;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _932_b), _932_b, _564_toTpe), selfIdent, @params, mustOwn, out _out462, out _out463, out _out464, out _out465);
                      s = _out462;
                      isOwned = _out463;
                      isErased = _out464;
                      readIdents = _out465;
                    }
                  }
                }
              } else if (_source38.is_Nullable) {
                DAST._IType _939___mcc_h531 = _source38.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _940_recursiveGen;
                  bool _941_recOwned;
                  bool _942_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _943_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out466;
                  bool _out467;
                  bool _out468;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out469;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out466, out _out467, out _out468, out _out469);
                  _940_recursiveGen = _out466;
                  _941_recOwned = _out467;
                  _942_recErased = _out468;
                  _943_recIdents = _out469;
                  if (!(_941_recOwned)) {
                    _940_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_940_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _940_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _942_recErased;
                  readIdents = _943_recIdents;
                }
              } else if (_source38.is_Tuple) {
                Dafny.ISequence<DAST._IType> _944___mcc_h533 = _source38.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _945_recursiveGen;
                  bool _946_recOwned;
                  bool _947_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _948_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out470;
                  bool _out471;
                  bool _out472;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out473;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out470, out _out471, out _out472, out _out473);
                  _945_recursiveGen = _out470;
                  _946_recOwned = _out471;
                  _947_recErased = _out472;
                  _948_recIdents = _out473;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _945_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _946_recOwned;
                  isErased = _947_recErased;
                  readIdents = _948_recIdents;
                }
              } else if (_source38.is_Array) {
                DAST._IType _949___mcc_h535 = _source38.dtor_element;
                BigInteger _950___mcc_h536 = _source38.dtor_dims;
                {
                  Dafny.ISequence<Dafny.Rune> _951_recursiveGen;
                  bool _952_recOwned;
                  bool _953_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _954_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out474;
                  bool _out475;
                  bool _out476;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out477;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out474, out _out475, out _out476, out _out477);
                  _951_recursiveGen = _out474;
                  _952_recOwned = _out475;
                  _953_recErased = _out476;
                  _954_recIdents = _out477;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _951_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _952_recOwned;
                  isErased = _953_recErased;
                  readIdents = _954_recIdents;
                }
              } else if (_source38.is_Seq) {
                DAST._IType _955___mcc_h539 = _source38.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _956_recursiveGen;
                  bool _957_recOwned;
                  bool _958_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _959_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out478;
                  bool _out479;
                  bool _out480;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out481;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out478, out _out479, out _out480, out _out481);
                  _956_recursiveGen = _out478;
                  _957_recOwned = _out479;
                  _958_recErased = _out480;
                  _959_recIdents = _out481;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _956_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _957_recOwned;
                  isErased = _958_recErased;
                  readIdents = _959_recIdents;
                }
              } else if (_source38.is_Set) {
                DAST._IType _960___mcc_h541 = _source38.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _961_recursiveGen;
                  bool _962_recOwned;
                  bool _963_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _964_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out482;
                  bool _out483;
                  bool _out484;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out485;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out482, out _out483, out _out484, out _out485);
                  _961_recursiveGen = _out482;
                  _962_recOwned = _out483;
                  _963_recErased = _out484;
                  _964_recIdents = _out485;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _961_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _962_recOwned;
                  isErased = _963_recErased;
                  readIdents = _964_recIdents;
                }
              } else if (_source38.is_Multiset) {
                DAST._IType _965___mcc_h543 = _source38.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _966_recursiveGen;
                  bool _967_recOwned;
                  bool _968_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _969_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out486;
                  bool _out487;
                  bool _out488;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out489;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out486, out _out487, out _out488, out _out489);
                  _966_recursiveGen = _out486;
                  _967_recOwned = _out487;
                  _968_recErased = _out488;
                  _969_recIdents = _out489;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _966_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _967_recOwned;
                  isErased = _968_recErased;
                  readIdents = _969_recIdents;
                }
              } else if (_source38.is_Map) {
                DAST._IType _970___mcc_h545 = _source38.dtor_key;
                DAST._IType _971___mcc_h546 = _source38.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _972_recursiveGen;
                  bool _973_recOwned;
                  bool _974_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _975_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out490;
                  bool _out491;
                  bool _out492;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out493;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out490, out _out491, out _out492, out _out493);
                  _972_recursiveGen = _out490;
                  _973_recOwned = _out491;
                  _974_recErased = _out492;
                  _975_recIdents = _out493;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _972_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _973_recOwned;
                  isErased = _974_recErased;
                  readIdents = _975_recIdents;
                }
              } else if (_source38.is_Arrow) {
                Dafny.ISequence<DAST._IType> _976___mcc_h549 = _source38.dtor_args;
                DAST._IType _977___mcc_h550 = _source38.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _978_recursiveGen;
                  bool _979_recOwned;
                  bool _980_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _981_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out494;
                  bool _out495;
                  bool _out496;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out497;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out494, out _out495, out _out496, out _out497);
                  _978_recursiveGen = _out494;
                  _979_recOwned = _out495;
                  _980_recErased = _out496;
                  _981_recIdents = _out497;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _978_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _979_recOwned;
                  isErased = _980_recErased;
                  readIdents = _981_recIdents;
                }
              } else if (_source38.is_Primitive) {
                DAST._IPrimitive _982___mcc_h553 = _source38.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _983_recursiveGen;
                  bool _984_recOwned;
                  bool _985_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _986_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out498;
                  bool _out499;
                  bool _out500;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out501;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out498, out _out499, out _out500, out _out501);
                  _983_recursiveGen = _out498;
                  _984_recOwned = _out499;
                  _985_recErased = _out500;
                  _986_recIdents = _out501;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _983_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _984_recOwned;
                  isErased = _985_recErased;
                  readIdents = _986_recIdents;
                }
              } else if (_source38.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _987___mcc_h555 = _source38.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _988_recursiveGen;
                  bool _989_recOwned;
                  bool _990_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _991_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out502;
                  bool _out503;
                  bool _out504;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out505;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out502, out _out503, out _out504, out _out505);
                  _988_recursiveGen = _out502;
                  _989_recOwned = _out503;
                  _990_recErased = _out504;
                  _991_recIdents = _out505;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _988_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _989_recOwned;
                  isErased = _990_recErased;
                  readIdents = _991_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _992___mcc_h557 = _source38.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _993_recursiveGen;
                  bool _994_recOwned;
                  bool _995_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _996_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out506;
                  bool _out507;
                  bool _out508;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out509;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out506, out _out507, out _out508, out _out509);
                  _993_recursiveGen = _out506;
                  _994_recOwned = _out507;
                  _995_recErased = _out508;
                  _996_recIdents = _out509;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _993_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _994_recOwned;
                  isErased = _995_recErased;
                  readIdents = _996_recIdents;
                }
              }
            } else if (_source28.is_Array) {
              DAST._IType _997___mcc_h559 = _source28.dtor_element;
              BigInteger _998___mcc_h560 = _source28.dtor_dims;
              DAST._IType _source40 = _572___mcc_h284;
              if (_source40.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _999___mcc_h567 = _source40.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1000___mcc_h568 = _source40.dtor_typeArgs;
                DAST._IResolvedType _1001___mcc_h569 = _source40.dtor_resolved;
                DAST._IResolvedType _source41 = _1001___mcc_h569;
                if (_source41.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1002___mcc_h573 = _source41.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1003_recursiveGen;
                    bool _1004_recOwned;
                    bool _1005_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1006_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out510;
                    bool _out511;
                    bool _out512;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out513;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out510, out _out511, out _out512, out _out513);
                    _1003_recursiveGen = _out510;
                    _1004_recOwned = _out511;
                    _1005_recErased = _out512;
                    _1006_recIdents = _out513;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1003_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1004_recOwned;
                    isErased = _1005_recErased;
                    readIdents = _1006_recIdents;
                  }
                } else if (_source41.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1007___mcc_h575 = _source41.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1008_recursiveGen;
                    bool _1009_recOwned;
                    bool _1010_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1011_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out514;
                    bool _out515;
                    bool _out516;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out517;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out514, out _out515, out _out516, out _out517);
                    _1008_recursiveGen = _out514;
                    _1009_recOwned = _out515;
                    _1010_recErased = _out516;
                    _1011_recIdents = _out517;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1008_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1009_recOwned;
                    isErased = _1010_recErased;
                    readIdents = _1011_recIdents;
                  }
                } else {
                  DAST._IType _1012___mcc_h577 = _source41.dtor_Newtype_a0;
                  DAST._IType _1013_b = _1012___mcc_h577;
                  {
                    if (object.Equals(_565_fromTpe, _1013_b)) {
                      Dafny.ISequence<Dafny.Rune> _1014_recursiveGen;
                      bool _1015_recOwned;
                      bool _1016_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1017_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out518;
                      bool _out519;
                      bool _out520;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out521;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out518, out _out519, out _out520, out _out521);
                      _1014_recursiveGen = _out518;
                      _1015_recOwned = _out519;
                      _1016_recErased = _out520;
                      _1017_recIdents = _out521;
                      Dafny.ISequence<Dafny.Rune> _1018_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out522;
                      _out522 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                      _1018_rhsType = _out522;
                      Dafny.ISequence<Dafny.Rune> _1019_uneraseFn;
                      _1019_uneraseFn = ((_1015_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1018_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1019_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1014_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1015_recOwned;
                      isErased = false;
                      readIdents = _1017_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out523;
                      bool _out524;
                      bool _out525;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out526;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _1013_b), _1013_b, _564_toTpe), selfIdent, @params, mustOwn, out _out523, out _out524, out _out525, out _out526);
                      s = _out523;
                      isOwned = _out524;
                      isErased = _out525;
                      readIdents = _out526;
                    }
                  }
                }
              } else if (_source40.is_Nullable) {
                DAST._IType _1020___mcc_h579 = _source40.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1021_recursiveGen;
                  bool _1022_recOwned;
                  bool _1023_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1024_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out527;
                  bool _out528;
                  bool _out529;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out530;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out527, out _out528, out _out529, out _out530);
                  _1021_recursiveGen = _out527;
                  _1022_recOwned = _out528;
                  _1023_recErased = _out529;
                  _1024_recIdents = _out530;
                  if (!(_1022_recOwned)) {
                    _1021_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1021_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1021_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1023_recErased;
                  readIdents = _1024_recIdents;
                }
              } else if (_source40.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1025___mcc_h581 = _source40.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1026_recursiveGen;
                  bool _1027_recOwned;
                  bool _1028_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1029_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out531;
                  bool _out532;
                  bool _out533;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out534;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out531, out _out532, out _out533, out _out534);
                  _1026_recursiveGen = _out531;
                  _1027_recOwned = _out532;
                  _1028_recErased = _out533;
                  _1029_recIdents = _out534;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1026_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1027_recOwned;
                  isErased = _1028_recErased;
                  readIdents = _1029_recIdents;
                }
              } else if (_source40.is_Array) {
                DAST._IType _1030___mcc_h583 = _source40.dtor_element;
                BigInteger _1031___mcc_h584 = _source40.dtor_dims;
                {
                  Dafny.ISequence<Dafny.Rune> _1032_recursiveGen;
                  bool _1033_recOwned;
                  bool _1034_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1035_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out535;
                  bool _out536;
                  bool _out537;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out538;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out535, out _out536, out _out537, out _out538);
                  _1032_recursiveGen = _out535;
                  _1033_recOwned = _out536;
                  _1034_recErased = _out537;
                  _1035_recIdents = _out538;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1032_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1033_recOwned;
                  isErased = _1034_recErased;
                  readIdents = _1035_recIdents;
                }
              } else if (_source40.is_Seq) {
                DAST._IType _1036___mcc_h587 = _source40.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1037_recursiveGen;
                  bool _1038_recOwned;
                  bool _1039_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1040_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out539;
                  bool _out540;
                  bool _out541;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out542;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out539, out _out540, out _out541, out _out542);
                  _1037_recursiveGen = _out539;
                  _1038_recOwned = _out540;
                  _1039_recErased = _out541;
                  _1040_recIdents = _out542;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1037_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1038_recOwned;
                  isErased = _1039_recErased;
                  readIdents = _1040_recIdents;
                }
              } else if (_source40.is_Set) {
                DAST._IType _1041___mcc_h589 = _source40.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1042_recursiveGen;
                  bool _1043_recOwned;
                  bool _1044_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1045_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out543;
                  bool _out544;
                  bool _out545;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out546;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out543, out _out544, out _out545, out _out546);
                  _1042_recursiveGen = _out543;
                  _1043_recOwned = _out544;
                  _1044_recErased = _out545;
                  _1045_recIdents = _out546;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1042_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1043_recOwned;
                  isErased = _1044_recErased;
                  readIdents = _1045_recIdents;
                }
              } else if (_source40.is_Multiset) {
                DAST._IType _1046___mcc_h591 = _source40.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1047_recursiveGen;
                  bool _1048_recOwned;
                  bool _1049_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1050_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out547;
                  bool _out548;
                  bool _out549;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out550;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out547, out _out548, out _out549, out _out550);
                  _1047_recursiveGen = _out547;
                  _1048_recOwned = _out548;
                  _1049_recErased = _out549;
                  _1050_recIdents = _out550;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1047_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1048_recOwned;
                  isErased = _1049_recErased;
                  readIdents = _1050_recIdents;
                }
              } else if (_source40.is_Map) {
                DAST._IType _1051___mcc_h593 = _source40.dtor_key;
                DAST._IType _1052___mcc_h594 = _source40.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1053_recursiveGen;
                  bool _1054_recOwned;
                  bool _1055_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1056_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out551;
                  bool _out552;
                  bool _out553;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out554;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out551, out _out552, out _out553, out _out554);
                  _1053_recursiveGen = _out551;
                  _1054_recOwned = _out552;
                  _1055_recErased = _out553;
                  _1056_recIdents = _out554;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1053_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1054_recOwned;
                  isErased = _1055_recErased;
                  readIdents = _1056_recIdents;
                }
              } else if (_source40.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1057___mcc_h597 = _source40.dtor_args;
                DAST._IType _1058___mcc_h598 = _source40.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1059_recursiveGen;
                  bool _1060_recOwned;
                  bool _1061_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1062_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out555;
                  bool _out556;
                  bool _out557;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out558;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out555, out _out556, out _out557, out _out558);
                  _1059_recursiveGen = _out555;
                  _1060_recOwned = _out556;
                  _1061_recErased = _out557;
                  _1062_recIdents = _out558;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1059_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1060_recOwned;
                  isErased = _1061_recErased;
                  readIdents = _1062_recIdents;
                }
              } else if (_source40.is_Primitive) {
                DAST._IPrimitive _1063___mcc_h601 = _source40.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1064_recursiveGen;
                  bool _1065_recOwned;
                  bool _1066_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1067_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out559;
                  bool _out560;
                  bool _out561;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out562;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out559, out _out560, out _out561, out _out562);
                  _1064_recursiveGen = _out559;
                  _1065_recOwned = _out560;
                  _1066_recErased = _out561;
                  _1067_recIdents = _out562;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1064_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1065_recOwned;
                  isErased = _1066_recErased;
                  readIdents = _1067_recIdents;
                }
              } else if (_source40.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1068___mcc_h603 = _source40.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1069_recursiveGen;
                  bool _1070_recOwned;
                  bool _1071_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1072_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out563;
                  bool _out564;
                  bool _out565;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out566;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out563, out _out564, out _out565, out _out566);
                  _1069_recursiveGen = _out563;
                  _1070_recOwned = _out564;
                  _1071_recErased = _out565;
                  _1072_recIdents = _out566;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1069_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1070_recOwned;
                  isErased = _1071_recErased;
                  readIdents = _1072_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1073___mcc_h605 = _source40.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1074_recursiveGen;
                  bool _1075_recOwned;
                  bool _1076_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1077_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out567;
                  bool _out568;
                  bool _out569;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out570;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out567, out _out568, out _out569, out _out570);
                  _1074_recursiveGen = _out567;
                  _1075_recOwned = _out568;
                  _1076_recErased = _out569;
                  _1077_recIdents = _out570;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1074_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1075_recOwned;
                  isErased = _1076_recErased;
                  readIdents = _1077_recIdents;
                }
              }
            } else if (_source28.is_Seq) {
              DAST._IType _1078___mcc_h607 = _source28.dtor_element;
              DAST._IType _source42 = _572___mcc_h284;
              if (_source42.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1079___mcc_h611 = _source42.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1080___mcc_h612 = _source42.dtor_typeArgs;
                DAST._IResolvedType _1081___mcc_h613 = _source42.dtor_resolved;
                DAST._IResolvedType _source43 = _1081___mcc_h613;
                if (_source43.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1082___mcc_h617 = _source43.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1083_recursiveGen;
                    bool _1084_recOwned;
                    bool _1085_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1086_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out571;
                    bool _out572;
                    bool _out573;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out574;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out571, out _out572, out _out573, out _out574);
                    _1083_recursiveGen = _out571;
                    _1084_recOwned = _out572;
                    _1085_recErased = _out573;
                    _1086_recIdents = _out574;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1083_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1084_recOwned;
                    isErased = _1085_recErased;
                    readIdents = _1086_recIdents;
                  }
                } else if (_source43.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1087___mcc_h619 = _source43.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1088_recursiveGen;
                    bool _1089_recOwned;
                    bool _1090_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1091_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out575;
                    bool _out576;
                    bool _out577;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out578;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out575, out _out576, out _out577, out _out578);
                    _1088_recursiveGen = _out575;
                    _1089_recOwned = _out576;
                    _1090_recErased = _out577;
                    _1091_recIdents = _out578;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1088_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1089_recOwned;
                    isErased = _1090_recErased;
                    readIdents = _1091_recIdents;
                  }
                } else {
                  DAST._IType _1092___mcc_h621 = _source43.dtor_Newtype_a0;
                  DAST._IType _1093_b = _1092___mcc_h621;
                  {
                    if (object.Equals(_565_fromTpe, _1093_b)) {
                      Dafny.ISequence<Dafny.Rune> _1094_recursiveGen;
                      bool _1095_recOwned;
                      bool _1096_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1097_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out579;
                      bool _out580;
                      bool _out581;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out582;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out579, out _out580, out _out581, out _out582);
                      _1094_recursiveGen = _out579;
                      _1095_recOwned = _out580;
                      _1096_recErased = _out581;
                      _1097_recIdents = _out582;
                      Dafny.ISequence<Dafny.Rune> _1098_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out583;
                      _out583 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                      _1098_rhsType = _out583;
                      Dafny.ISequence<Dafny.Rune> _1099_uneraseFn;
                      _1099_uneraseFn = ((_1095_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1098_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1099_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1094_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1095_recOwned;
                      isErased = false;
                      readIdents = _1097_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out584;
                      bool _out585;
                      bool _out586;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out587;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _1093_b), _1093_b, _564_toTpe), selfIdent, @params, mustOwn, out _out584, out _out585, out _out586, out _out587);
                      s = _out584;
                      isOwned = _out585;
                      isErased = _out586;
                      readIdents = _out587;
                    }
                  }
                }
              } else if (_source42.is_Nullable) {
                DAST._IType _1100___mcc_h623 = _source42.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1101_recursiveGen;
                  bool _1102_recOwned;
                  bool _1103_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1104_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out588;
                  bool _out589;
                  bool _out590;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out591;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out588, out _out589, out _out590, out _out591);
                  _1101_recursiveGen = _out588;
                  _1102_recOwned = _out589;
                  _1103_recErased = _out590;
                  _1104_recIdents = _out591;
                  if (!(_1102_recOwned)) {
                    _1101_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1101_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1101_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1103_recErased;
                  readIdents = _1104_recIdents;
                }
              } else if (_source42.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1105___mcc_h625 = _source42.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1106_recursiveGen;
                  bool _1107_recOwned;
                  bool _1108_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1109_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out592;
                  bool _out593;
                  bool _out594;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out595;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out592, out _out593, out _out594, out _out595);
                  _1106_recursiveGen = _out592;
                  _1107_recOwned = _out593;
                  _1108_recErased = _out594;
                  _1109_recIdents = _out595;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1106_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1107_recOwned;
                  isErased = _1108_recErased;
                  readIdents = _1109_recIdents;
                }
              } else if (_source42.is_Array) {
                DAST._IType _1110___mcc_h627 = _source42.dtor_element;
                BigInteger _1111___mcc_h628 = _source42.dtor_dims;
                {
                  Dafny.ISequence<Dafny.Rune> _1112_recursiveGen;
                  bool _1113_recOwned;
                  bool _1114_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1115_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out596;
                  bool _out597;
                  bool _out598;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out599;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out596, out _out597, out _out598, out _out599);
                  _1112_recursiveGen = _out596;
                  _1113_recOwned = _out597;
                  _1114_recErased = _out598;
                  _1115_recIdents = _out599;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1112_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1113_recOwned;
                  isErased = _1114_recErased;
                  readIdents = _1115_recIdents;
                }
              } else if (_source42.is_Seq) {
                DAST._IType _1116___mcc_h631 = _source42.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1117_recursiveGen;
                  bool _1118_recOwned;
                  bool _1119_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1120_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out600;
                  bool _out601;
                  bool _out602;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out603;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out600, out _out601, out _out602, out _out603);
                  _1117_recursiveGen = _out600;
                  _1118_recOwned = _out601;
                  _1119_recErased = _out602;
                  _1120_recIdents = _out603;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1117_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1118_recOwned;
                  isErased = _1119_recErased;
                  readIdents = _1120_recIdents;
                }
              } else if (_source42.is_Set) {
                DAST._IType _1121___mcc_h633 = _source42.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1122_recursiveGen;
                  bool _1123_recOwned;
                  bool _1124_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1125_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out604;
                  bool _out605;
                  bool _out606;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out607;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out604, out _out605, out _out606, out _out607);
                  _1122_recursiveGen = _out604;
                  _1123_recOwned = _out605;
                  _1124_recErased = _out606;
                  _1125_recIdents = _out607;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1122_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1123_recOwned;
                  isErased = _1124_recErased;
                  readIdents = _1125_recIdents;
                }
              } else if (_source42.is_Multiset) {
                DAST._IType _1126___mcc_h635 = _source42.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1127_recursiveGen;
                  bool _1128_recOwned;
                  bool _1129_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1130_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out608;
                  bool _out609;
                  bool _out610;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out611;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out608, out _out609, out _out610, out _out611);
                  _1127_recursiveGen = _out608;
                  _1128_recOwned = _out609;
                  _1129_recErased = _out610;
                  _1130_recIdents = _out611;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1127_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1128_recOwned;
                  isErased = _1129_recErased;
                  readIdents = _1130_recIdents;
                }
              } else if (_source42.is_Map) {
                DAST._IType _1131___mcc_h637 = _source42.dtor_key;
                DAST._IType _1132___mcc_h638 = _source42.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1133_recursiveGen;
                  bool _1134_recOwned;
                  bool _1135_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1136_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out612;
                  bool _out613;
                  bool _out614;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out615;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out612, out _out613, out _out614, out _out615);
                  _1133_recursiveGen = _out612;
                  _1134_recOwned = _out613;
                  _1135_recErased = _out614;
                  _1136_recIdents = _out615;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1133_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1134_recOwned;
                  isErased = _1135_recErased;
                  readIdents = _1136_recIdents;
                }
              } else if (_source42.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1137___mcc_h641 = _source42.dtor_args;
                DAST._IType _1138___mcc_h642 = _source42.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1139_recursiveGen;
                  bool _1140_recOwned;
                  bool _1141_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1142_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out616;
                  bool _out617;
                  bool _out618;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out619;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out616, out _out617, out _out618, out _out619);
                  _1139_recursiveGen = _out616;
                  _1140_recOwned = _out617;
                  _1141_recErased = _out618;
                  _1142_recIdents = _out619;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1139_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1140_recOwned;
                  isErased = _1141_recErased;
                  readIdents = _1142_recIdents;
                }
              } else if (_source42.is_Primitive) {
                DAST._IPrimitive _1143___mcc_h645 = _source42.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1144_recursiveGen;
                  bool _1145_recOwned;
                  bool _1146_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1147_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out620;
                  bool _out621;
                  bool _out622;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out623;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out620, out _out621, out _out622, out _out623);
                  _1144_recursiveGen = _out620;
                  _1145_recOwned = _out621;
                  _1146_recErased = _out622;
                  _1147_recIdents = _out623;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1144_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1145_recOwned;
                  isErased = _1146_recErased;
                  readIdents = _1147_recIdents;
                }
              } else if (_source42.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1148___mcc_h647 = _source42.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1149_recursiveGen;
                  bool _1150_recOwned;
                  bool _1151_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1152_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out624;
                  bool _out625;
                  bool _out626;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out627;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out624, out _out625, out _out626, out _out627);
                  _1149_recursiveGen = _out624;
                  _1150_recOwned = _out625;
                  _1151_recErased = _out626;
                  _1152_recIdents = _out627;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1149_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1150_recOwned;
                  isErased = _1151_recErased;
                  readIdents = _1152_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1153___mcc_h649 = _source42.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1154_recursiveGen;
                  bool _1155_recOwned;
                  bool _1156_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1157_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out628;
                  bool _out629;
                  bool _out630;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out631;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out628, out _out629, out _out630, out _out631);
                  _1154_recursiveGen = _out628;
                  _1155_recOwned = _out629;
                  _1156_recErased = _out630;
                  _1157_recIdents = _out631;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1154_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1155_recOwned;
                  isErased = _1156_recErased;
                  readIdents = _1157_recIdents;
                }
              }
            } else if (_source28.is_Set) {
              DAST._IType _1158___mcc_h651 = _source28.dtor_element;
              DAST._IType _source44 = _572___mcc_h284;
              if (_source44.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1159___mcc_h655 = _source44.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1160___mcc_h656 = _source44.dtor_typeArgs;
                DAST._IResolvedType _1161___mcc_h657 = _source44.dtor_resolved;
                DAST._IResolvedType _source45 = _1161___mcc_h657;
                if (_source45.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1162___mcc_h661 = _source45.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1163_recursiveGen;
                    bool _1164_recOwned;
                    bool _1165_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1166_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out632;
                    bool _out633;
                    bool _out634;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out635;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out632, out _out633, out _out634, out _out635);
                    _1163_recursiveGen = _out632;
                    _1164_recOwned = _out633;
                    _1165_recErased = _out634;
                    _1166_recIdents = _out635;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1163_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1164_recOwned;
                    isErased = _1165_recErased;
                    readIdents = _1166_recIdents;
                  }
                } else if (_source45.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1167___mcc_h663 = _source45.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1168_recursiveGen;
                    bool _1169_recOwned;
                    bool _1170_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1171_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out636;
                    bool _out637;
                    bool _out638;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out639;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out636, out _out637, out _out638, out _out639);
                    _1168_recursiveGen = _out636;
                    _1169_recOwned = _out637;
                    _1170_recErased = _out638;
                    _1171_recIdents = _out639;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1168_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1169_recOwned;
                    isErased = _1170_recErased;
                    readIdents = _1171_recIdents;
                  }
                } else {
                  DAST._IType _1172___mcc_h665 = _source45.dtor_Newtype_a0;
                  DAST._IType _1173_b = _1172___mcc_h665;
                  {
                    if (object.Equals(_565_fromTpe, _1173_b)) {
                      Dafny.ISequence<Dafny.Rune> _1174_recursiveGen;
                      bool _1175_recOwned;
                      bool _1176_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1177_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out640;
                      bool _out641;
                      bool _out642;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out643;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out640, out _out641, out _out642, out _out643);
                      _1174_recursiveGen = _out640;
                      _1175_recOwned = _out641;
                      _1176_recErased = _out642;
                      _1177_recIdents = _out643;
                      Dafny.ISequence<Dafny.Rune> _1178_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out644;
                      _out644 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                      _1178_rhsType = _out644;
                      Dafny.ISequence<Dafny.Rune> _1179_uneraseFn;
                      _1179_uneraseFn = ((_1175_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1178_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1179_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1174_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1175_recOwned;
                      isErased = false;
                      readIdents = _1177_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out645;
                      bool _out646;
                      bool _out647;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out648;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _1173_b), _1173_b, _564_toTpe), selfIdent, @params, mustOwn, out _out645, out _out646, out _out647, out _out648);
                      s = _out645;
                      isOwned = _out646;
                      isErased = _out647;
                      readIdents = _out648;
                    }
                  }
                }
              } else if (_source44.is_Nullable) {
                DAST._IType _1180___mcc_h667 = _source44.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1181_recursiveGen;
                  bool _1182_recOwned;
                  bool _1183_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1184_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out649;
                  bool _out650;
                  bool _out651;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out652;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out649, out _out650, out _out651, out _out652);
                  _1181_recursiveGen = _out649;
                  _1182_recOwned = _out650;
                  _1183_recErased = _out651;
                  _1184_recIdents = _out652;
                  if (!(_1182_recOwned)) {
                    _1181_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1181_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1181_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1183_recErased;
                  readIdents = _1184_recIdents;
                }
              } else if (_source44.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1185___mcc_h669 = _source44.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1186_recursiveGen;
                  bool _1187_recOwned;
                  bool _1188_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1189_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out653;
                  bool _out654;
                  bool _out655;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out656;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out653, out _out654, out _out655, out _out656);
                  _1186_recursiveGen = _out653;
                  _1187_recOwned = _out654;
                  _1188_recErased = _out655;
                  _1189_recIdents = _out656;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1186_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1187_recOwned;
                  isErased = _1188_recErased;
                  readIdents = _1189_recIdents;
                }
              } else if (_source44.is_Array) {
                DAST._IType _1190___mcc_h671 = _source44.dtor_element;
                BigInteger _1191___mcc_h672 = _source44.dtor_dims;
                {
                  Dafny.ISequence<Dafny.Rune> _1192_recursiveGen;
                  bool _1193_recOwned;
                  bool _1194_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1195_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out657;
                  bool _out658;
                  bool _out659;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out660;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out657, out _out658, out _out659, out _out660);
                  _1192_recursiveGen = _out657;
                  _1193_recOwned = _out658;
                  _1194_recErased = _out659;
                  _1195_recIdents = _out660;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1192_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1193_recOwned;
                  isErased = _1194_recErased;
                  readIdents = _1195_recIdents;
                }
              } else if (_source44.is_Seq) {
                DAST._IType _1196___mcc_h675 = _source44.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1197_recursiveGen;
                  bool _1198_recOwned;
                  bool _1199_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1200_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out661;
                  bool _out662;
                  bool _out663;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out664;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out661, out _out662, out _out663, out _out664);
                  _1197_recursiveGen = _out661;
                  _1198_recOwned = _out662;
                  _1199_recErased = _out663;
                  _1200_recIdents = _out664;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1197_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1198_recOwned;
                  isErased = _1199_recErased;
                  readIdents = _1200_recIdents;
                }
              } else if (_source44.is_Set) {
                DAST._IType _1201___mcc_h677 = _source44.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1202_recursiveGen;
                  bool _1203_recOwned;
                  bool _1204_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1205_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out665;
                  bool _out666;
                  bool _out667;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out668;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out665, out _out666, out _out667, out _out668);
                  _1202_recursiveGen = _out665;
                  _1203_recOwned = _out666;
                  _1204_recErased = _out667;
                  _1205_recIdents = _out668;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1202_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1203_recOwned;
                  isErased = _1204_recErased;
                  readIdents = _1205_recIdents;
                }
              } else if (_source44.is_Multiset) {
                DAST._IType _1206___mcc_h679 = _source44.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1207_recursiveGen;
                  bool _1208_recOwned;
                  bool _1209_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1210_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out669;
                  bool _out670;
                  bool _out671;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out672;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out669, out _out670, out _out671, out _out672);
                  _1207_recursiveGen = _out669;
                  _1208_recOwned = _out670;
                  _1209_recErased = _out671;
                  _1210_recIdents = _out672;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1207_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1208_recOwned;
                  isErased = _1209_recErased;
                  readIdents = _1210_recIdents;
                }
              } else if (_source44.is_Map) {
                DAST._IType _1211___mcc_h681 = _source44.dtor_key;
                DAST._IType _1212___mcc_h682 = _source44.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1213_recursiveGen;
                  bool _1214_recOwned;
                  bool _1215_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1216_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out673;
                  bool _out674;
                  bool _out675;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out676;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out673, out _out674, out _out675, out _out676);
                  _1213_recursiveGen = _out673;
                  _1214_recOwned = _out674;
                  _1215_recErased = _out675;
                  _1216_recIdents = _out676;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1213_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1214_recOwned;
                  isErased = _1215_recErased;
                  readIdents = _1216_recIdents;
                }
              } else if (_source44.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1217___mcc_h685 = _source44.dtor_args;
                DAST._IType _1218___mcc_h686 = _source44.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1219_recursiveGen;
                  bool _1220_recOwned;
                  bool _1221_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1222_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out677;
                  bool _out678;
                  bool _out679;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out680;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out677, out _out678, out _out679, out _out680);
                  _1219_recursiveGen = _out677;
                  _1220_recOwned = _out678;
                  _1221_recErased = _out679;
                  _1222_recIdents = _out680;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1219_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1220_recOwned;
                  isErased = _1221_recErased;
                  readIdents = _1222_recIdents;
                }
              } else if (_source44.is_Primitive) {
                DAST._IPrimitive _1223___mcc_h689 = _source44.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1224_recursiveGen;
                  bool _1225_recOwned;
                  bool _1226_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1227_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out681;
                  bool _out682;
                  bool _out683;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out684;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out681, out _out682, out _out683, out _out684);
                  _1224_recursiveGen = _out681;
                  _1225_recOwned = _out682;
                  _1226_recErased = _out683;
                  _1227_recIdents = _out684;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1224_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1225_recOwned;
                  isErased = _1226_recErased;
                  readIdents = _1227_recIdents;
                }
              } else if (_source44.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1228___mcc_h691 = _source44.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1229_recursiveGen;
                  bool _1230_recOwned;
                  bool _1231_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1232_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out685;
                  bool _out686;
                  bool _out687;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out688;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out685, out _out686, out _out687, out _out688);
                  _1229_recursiveGen = _out685;
                  _1230_recOwned = _out686;
                  _1231_recErased = _out687;
                  _1232_recIdents = _out688;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1229_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1230_recOwned;
                  isErased = _1231_recErased;
                  readIdents = _1232_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1233___mcc_h693 = _source44.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1234_recursiveGen;
                  bool _1235_recOwned;
                  bool _1236_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1237_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out689;
                  bool _out690;
                  bool _out691;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out692;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out689, out _out690, out _out691, out _out692);
                  _1234_recursiveGen = _out689;
                  _1235_recOwned = _out690;
                  _1236_recErased = _out691;
                  _1237_recIdents = _out692;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1234_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1235_recOwned;
                  isErased = _1236_recErased;
                  readIdents = _1237_recIdents;
                }
              }
            } else if (_source28.is_Multiset) {
              DAST._IType _1238___mcc_h695 = _source28.dtor_element;
              DAST._IType _source46 = _572___mcc_h284;
              if (_source46.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1239___mcc_h699 = _source46.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1240___mcc_h700 = _source46.dtor_typeArgs;
                DAST._IResolvedType _1241___mcc_h701 = _source46.dtor_resolved;
                DAST._IResolvedType _source47 = _1241___mcc_h701;
                if (_source47.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1242___mcc_h705 = _source47.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1243_recursiveGen;
                    bool _1244_recOwned;
                    bool _1245_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1246_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out693;
                    bool _out694;
                    bool _out695;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out696;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out693, out _out694, out _out695, out _out696);
                    _1243_recursiveGen = _out693;
                    _1244_recOwned = _out694;
                    _1245_recErased = _out695;
                    _1246_recIdents = _out696;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1243_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1244_recOwned;
                    isErased = _1245_recErased;
                    readIdents = _1246_recIdents;
                  }
                } else if (_source47.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1247___mcc_h707 = _source47.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1248_recursiveGen;
                    bool _1249_recOwned;
                    bool _1250_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1251_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out697;
                    bool _out698;
                    bool _out699;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out700;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out697, out _out698, out _out699, out _out700);
                    _1248_recursiveGen = _out697;
                    _1249_recOwned = _out698;
                    _1250_recErased = _out699;
                    _1251_recIdents = _out700;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1248_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1249_recOwned;
                    isErased = _1250_recErased;
                    readIdents = _1251_recIdents;
                  }
                } else {
                  DAST._IType _1252___mcc_h709 = _source47.dtor_Newtype_a0;
                  DAST._IType _1253_b = _1252___mcc_h709;
                  {
                    if (object.Equals(_565_fromTpe, _1253_b)) {
                      Dafny.ISequence<Dafny.Rune> _1254_recursiveGen;
                      bool _1255_recOwned;
                      bool _1256_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1257_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out701;
                      bool _out702;
                      bool _out703;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out704;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out701, out _out702, out _out703, out _out704);
                      _1254_recursiveGen = _out701;
                      _1255_recOwned = _out702;
                      _1256_recErased = _out703;
                      _1257_recIdents = _out704;
                      Dafny.ISequence<Dafny.Rune> _1258_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out705;
                      _out705 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                      _1258_rhsType = _out705;
                      Dafny.ISequence<Dafny.Rune> _1259_uneraseFn;
                      _1259_uneraseFn = ((_1255_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1258_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1259_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1254_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1255_recOwned;
                      isErased = false;
                      readIdents = _1257_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out706;
                      bool _out707;
                      bool _out708;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out709;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _1253_b), _1253_b, _564_toTpe), selfIdent, @params, mustOwn, out _out706, out _out707, out _out708, out _out709);
                      s = _out706;
                      isOwned = _out707;
                      isErased = _out708;
                      readIdents = _out709;
                    }
                  }
                }
              } else if (_source46.is_Nullable) {
                DAST._IType _1260___mcc_h711 = _source46.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1261_recursiveGen;
                  bool _1262_recOwned;
                  bool _1263_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1264_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out710;
                  bool _out711;
                  bool _out712;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out713;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out710, out _out711, out _out712, out _out713);
                  _1261_recursiveGen = _out710;
                  _1262_recOwned = _out711;
                  _1263_recErased = _out712;
                  _1264_recIdents = _out713;
                  if (!(_1262_recOwned)) {
                    _1261_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1261_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1261_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1263_recErased;
                  readIdents = _1264_recIdents;
                }
              } else if (_source46.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1265___mcc_h713 = _source46.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1266_recursiveGen;
                  bool _1267_recOwned;
                  bool _1268_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1269_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out714;
                  bool _out715;
                  bool _out716;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out717;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out714, out _out715, out _out716, out _out717);
                  _1266_recursiveGen = _out714;
                  _1267_recOwned = _out715;
                  _1268_recErased = _out716;
                  _1269_recIdents = _out717;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1266_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1267_recOwned;
                  isErased = _1268_recErased;
                  readIdents = _1269_recIdents;
                }
              } else if (_source46.is_Array) {
                DAST._IType _1270___mcc_h715 = _source46.dtor_element;
                BigInteger _1271___mcc_h716 = _source46.dtor_dims;
                {
                  Dafny.ISequence<Dafny.Rune> _1272_recursiveGen;
                  bool _1273_recOwned;
                  bool _1274_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1275_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out718;
                  bool _out719;
                  bool _out720;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out721;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out718, out _out719, out _out720, out _out721);
                  _1272_recursiveGen = _out718;
                  _1273_recOwned = _out719;
                  _1274_recErased = _out720;
                  _1275_recIdents = _out721;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1272_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1273_recOwned;
                  isErased = _1274_recErased;
                  readIdents = _1275_recIdents;
                }
              } else if (_source46.is_Seq) {
                DAST._IType _1276___mcc_h719 = _source46.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1277_recursiveGen;
                  bool _1278_recOwned;
                  bool _1279_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1280_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out722;
                  bool _out723;
                  bool _out724;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out725;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out722, out _out723, out _out724, out _out725);
                  _1277_recursiveGen = _out722;
                  _1278_recOwned = _out723;
                  _1279_recErased = _out724;
                  _1280_recIdents = _out725;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1277_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1278_recOwned;
                  isErased = _1279_recErased;
                  readIdents = _1280_recIdents;
                }
              } else if (_source46.is_Set) {
                DAST._IType _1281___mcc_h721 = _source46.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1282_recursiveGen;
                  bool _1283_recOwned;
                  bool _1284_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1285_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out726;
                  bool _out727;
                  bool _out728;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out729;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out726, out _out727, out _out728, out _out729);
                  _1282_recursiveGen = _out726;
                  _1283_recOwned = _out727;
                  _1284_recErased = _out728;
                  _1285_recIdents = _out729;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1282_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1283_recOwned;
                  isErased = _1284_recErased;
                  readIdents = _1285_recIdents;
                }
              } else if (_source46.is_Multiset) {
                DAST._IType _1286___mcc_h723 = _source46.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1287_recursiveGen;
                  bool _1288_recOwned;
                  bool _1289_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1290_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out730;
                  bool _out731;
                  bool _out732;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out733;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out730, out _out731, out _out732, out _out733);
                  _1287_recursiveGen = _out730;
                  _1288_recOwned = _out731;
                  _1289_recErased = _out732;
                  _1290_recIdents = _out733;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1287_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1288_recOwned;
                  isErased = _1289_recErased;
                  readIdents = _1290_recIdents;
                }
              } else if (_source46.is_Map) {
                DAST._IType _1291___mcc_h725 = _source46.dtor_key;
                DAST._IType _1292___mcc_h726 = _source46.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1293_recursiveGen;
                  bool _1294_recOwned;
                  bool _1295_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1296_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out734;
                  bool _out735;
                  bool _out736;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out737;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out734, out _out735, out _out736, out _out737);
                  _1293_recursiveGen = _out734;
                  _1294_recOwned = _out735;
                  _1295_recErased = _out736;
                  _1296_recIdents = _out737;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1293_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1294_recOwned;
                  isErased = _1295_recErased;
                  readIdents = _1296_recIdents;
                }
              } else if (_source46.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1297___mcc_h729 = _source46.dtor_args;
                DAST._IType _1298___mcc_h730 = _source46.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1299_recursiveGen;
                  bool _1300_recOwned;
                  bool _1301_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1302_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out738;
                  bool _out739;
                  bool _out740;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out741;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out738, out _out739, out _out740, out _out741);
                  _1299_recursiveGen = _out738;
                  _1300_recOwned = _out739;
                  _1301_recErased = _out740;
                  _1302_recIdents = _out741;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1299_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1300_recOwned;
                  isErased = _1301_recErased;
                  readIdents = _1302_recIdents;
                }
              } else if (_source46.is_Primitive) {
                DAST._IPrimitive _1303___mcc_h733 = _source46.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1304_recursiveGen;
                  bool _1305_recOwned;
                  bool _1306_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1307_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out742;
                  bool _out743;
                  bool _out744;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out745;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out742, out _out743, out _out744, out _out745);
                  _1304_recursiveGen = _out742;
                  _1305_recOwned = _out743;
                  _1306_recErased = _out744;
                  _1307_recIdents = _out745;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1304_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1305_recOwned;
                  isErased = _1306_recErased;
                  readIdents = _1307_recIdents;
                }
              } else if (_source46.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1308___mcc_h735 = _source46.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1309_recursiveGen;
                  bool _1310_recOwned;
                  bool _1311_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1312_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out746;
                  bool _out747;
                  bool _out748;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out749;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out746, out _out747, out _out748, out _out749);
                  _1309_recursiveGen = _out746;
                  _1310_recOwned = _out747;
                  _1311_recErased = _out748;
                  _1312_recIdents = _out749;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1309_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1310_recOwned;
                  isErased = _1311_recErased;
                  readIdents = _1312_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1313___mcc_h737 = _source46.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1314_recursiveGen;
                  bool _1315_recOwned;
                  bool _1316_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1317_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out750;
                  bool _out751;
                  bool _out752;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out753;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out750, out _out751, out _out752, out _out753);
                  _1314_recursiveGen = _out750;
                  _1315_recOwned = _out751;
                  _1316_recErased = _out752;
                  _1317_recIdents = _out753;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1314_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1315_recOwned;
                  isErased = _1316_recErased;
                  readIdents = _1317_recIdents;
                }
              }
            } else if (_source28.is_Map) {
              DAST._IType _1318___mcc_h739 = _source28.dtor_key;
              DAST._IType _1319___mcc_h740 = _source28.dtor_value;
              DAST._IType _source48 = _572___mcc_h284;
              if (_source48.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1320___mcc_h747 = _source48.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1321___mcc_h748 = _source48.dtor_typeArgs;
                DAST._IResolvedType _1322___mcc_h749 = _source48.dtor_resolved;
                DAST._IResolvedType _source49 = _1322___mcc_h749;
                if (_source49.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1323___mcc_h753 = _source49.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1324_recursiveGen;
                    bool _1325_recOwned;
                    bool _1326_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1327_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out754;
                    bool _out755;
                    bool _out756;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out757;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out754, out _out755, out _out756, out _out757);
                    _1324_recursiveGen = _out754;
                    _1325_recOwned = _out755;
                    _1326_recErased = _out756;
                    _1327_recIdents = _out757;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1324_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1325_recOwned;
                    isErased = _1326_recErased;
                    readIdents = _1327_recIdents;
                  }
                } else if (_source49.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1328___mcc_h755 = _source49.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1329_recursiveGen;
                    bool _1330_recOwned;
                    bool _1331_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1332_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out758;
                    bool _out759;
                    bool _out760;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out761;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out758, out _out759, out _out760, out _out761);
                    _1329_recursiveGen = _out758;
                    _1330_recOwned = _out759;
                    _1331_recErased = _out760;
                    _1332_recIdents = _out761;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1329_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1330_recOwned;
                    isErased = _1331_recErased;
                    readIdents = _1332_recIdents;
                  }
                } else {
                  DAST._IType _1333___mcc_h757 = _source49.dtor_Newtype_a0;
                  DAST._IType _1334_b = _1333___mcc_h757;
                  {
                    if (object.Equals(_565_fromTpe, _1334_b)) {
                      Dafny.ISequence<Dafny.Rune> _1335_recursiveGen;
                      bool _1336_recOwned;
                      bool _1337_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1338_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out762;
                      bool _out763;
                      bool _out764;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out765;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out762, out _out763, out _out764, out _out765);
                      _1335_recursiveGen = _out762;
                      _1336_recOwned = _out763;
                      _1337_recErased = _out764;
                      _1338_recIdents = _out765;
                      Dafny.ISequence<Dafny.Rune> _1339_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out766;
                      _out766 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                      _1339_rhsType = _out766;
                      Dafny.ISequence<Dafny.Rune> _1340_uneraseFn;
                      _1340_uneraseFn = ((_1336_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1339_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1340_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1335_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1336_recOwned;
                      isErased = false;
                      readIdents = _1338_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out767;
                      bool _out768;
                      bool _out769;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out770;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _1334_b), _1334_b, _564_toTpe), selfIdent, @params, mustOwn, out _out767, out _out768, out _out769, out _out770);
                      s = _out767;
                      isOwned = _out768;
                      isErased = _out769;
                      readIdents = _out770;
                    }
                  }
                }
              } else if (_source48.is_Nullable) {
                DAST._IType _1341___mcc_h759 = _source48.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1342_recursiveGen;
                  bool _1343_recOwned;
                  bool _1344_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1345_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out771;
                  bool _out772;
                  bool _out773;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out774;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out771, out _out772, out _out773, out _out774);
                  _1342_recursiveGen = _out771;
                  _1343_recOwned = _out772;
                  _1344_recErased = _out773;
                  _1345_recIdents = _out774;
                  if (!(_1343_recOwned)) {
                    _1342_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1342_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1342_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1344_recErased;
                  readIdents = _1345_recIdents;
                }
              } else if (_source48.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1346___mcc_h761 = _source48.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1347_recursiveGen;
                  bool _1348_recOwned;
                  bool _1349_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1350_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out775;
                  bool _out776;
                  bool _out777;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out778;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out775, out _out776, out _out777, out _out778);
                  _1347_recursiveGen = _out775;
                  _1348_recOwned = _out776;
                  _1349_recErased = _out777;
                  _1350_recIdents = _out778;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1347_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1348_recOwned;
                  isErased = _1349_recErased;
                  readIdents = _1350_recIdents;
                }
              } else if (_source48.is_Array) {
                DAST._IType _1351___mcc_h763 = _source48.dtor_element;
                BigInteger _1352___mcc_h764 = _source48.dtor_dims;
                {
                  Dafny.ISequence<Dafny.Rune> _1353_recursiveGen;
                  bool _1354_recOwned;
                  bool _1355_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1356_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out779;
                  bool _out780;
                  bool _out781;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out782;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out779, out _out780, out _out781, out _out782);
                  _1353_recursiveGen = _out779;
                  _1354_recOwned = _out780;
                  _1355_recErased = _out781;
                  _1356_recIdents = _out782;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1353_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1354_recOwned;
                  isErased = _1355_recErased;
                  readIdents = _1356_recIdents;
                }
              } else if (_source48.is_Seq) {
                DAST._IType _1357___mcc_h767 = _source48.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1358_recursiveGen;
                  bool _1359_recOwned;
                  bool _1360_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1361_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out783;
                  bool _out784;
                  bool _out785;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out786;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out783, out _out784, out _out785, out _out786);
                  _1358_recursiveGen = _out783;
                  _1359_recOwned = _out784;
                  _1360_recErased = _out785;
                  _1361_recIdents = _out786;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1358_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1359_recOwned;
                  isErased = _1360_recErased;
                  readIdents = _1361_recIdents;
                }
              } else if (_source48.is_Set) {
                DAST._IType _1362___mcc_h769 = _source48.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1363_recursiveGen;
                  bool _1364_recOwned;
                  bool _1365_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1366_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out787;
                  bool _out788;
                  bool _out789;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out790;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out787, out _out788, out _out789, out _out790);
                  _1363_recursiveGen = _out787;
                  _1364_recOwned = _out788;
                  _1365_recErased = _out789;
                  _1366_recIdents = _out790;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1363_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1364_recOwned;
                  isErased = _1365_recErased;
                  readIdents = _1366_recIdents;
                }
              } else if (_source48.is_Multiset) {
                DAST._IType _1367___mcc_h771 = _source48.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1368_recursiveGen;
                  bool _1369_recOwned;
                  bool _1370_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1371_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out791;
                  bool _out792;
                  bool _out793;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out794;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out791, out _out792, out _out793, out _out794);
                  _1368_recursiveGen = _out791;
                  _1369_recOwned = _out792;
                  _1370_recErased = _out793;
                  _1371_recIdents = _out794;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1368_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1369_recOwned;
                  isErased = _1370_recErased;
                  readIdents = _1371_recIdents;
                }
              } else if (_source48.is_Map) {
                DAST._IType _1372___mcc_h773 = _source48.dtor_key;
                DAST._IType _1373___mcc_h774 = _source48.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1374_recursiveGen;
                  bool _1375_recOwned;
                  bool _1376_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1377_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out795;
                  bool _out796;
                  bool _out797;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out798;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out795, out _out796, out _out797, out _out798);
                  _1374_recursiveGen = _out795;
                  _1375_recOwned = _out796;
                  _1376_recErased = _out797;
                  _1377_recIdents = _out798;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1374_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1375_recOwned;
                  isErased = _1376_recErased;
                  readIdents = _1377_recIdents;
                }
              } else if (_source48.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1378___mcc_h777 = _source48.dtor_args;
                DAST._IType _1379___mcc_h778 = _source48.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1380_recursiveGen;
                  bool _1381_recOwned;
                  bool _1382_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1383_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out799;
                  bool _out800;
                  bool _out801;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out802;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out799, out _out800, out _out801, out _out802);
                  _1380_recursiveGen = _out799;
                  _1381_recOwned = _out800;
                  _1382_recErased = _out801;
                  _1383_recIdents = _out802;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1380_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1381_recOwned;
                  isErased = _1382_recErased;
                  readIdents = _1383_recIdents;
                }
              } else if (_source48.is_Primitive) {
                DAST._IPrimitive _1384___mcc_h781 = _source48.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1385_recursiveGen;
                  bool _1386_recOwned;
                  bool _1387_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1388_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out803;
                  bool _out804;
                  bool _out805;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out806;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out803, out _out804, out _out805, out _out806);
                  _1385_recursiveGen = _out803;
                  _1386_recOwned = _out804;
                  _1387_recErased = _out805;
                  _1388_recIdents = _out806;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1385_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1386_recOwned;
                  isErased = _1387_recErased;
                  readIdents = _1388_recIdents;
                }
              } else if (_source48.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1389___mcc_h783 = _source48.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1390_recursiveGen;
                  bool _1391_recOwned;
                  bool _1392_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1393_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out807;
                  bool _out808;
                  bool _out809;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out810;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out807, out _out808, out _out809, out _out810);
                  _1390_recursiveGen = _out807;
                  _1391_recOwned = _out808;
                  _1392_recErased = _out809;
                  _1393_recIdents = _out810;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1390_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1391_recOwned;
                  isErased = _1392_recErased;
                  readIdents = _1393_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1394___mcc_h785 = _source48.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1395_recursiveGen;
                  bool _1396_recOwned;
                  bool _1397_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1398_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out811;
                  bool _out812;
                  bool _out813;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out814;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out811, out _out812, out _out813, out _out814);
                  _1395_recursiveGen = _out811;
                  _1396_recOwned = _out812;
                  _1397_recErased = _out813;
                  _1398_recIdents = _out814;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1395_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1396_recOwned;
                  isErased = _1397_recErased;
                  readIdents = _1398_recIdents;
                }
              }
            } else if (_source28.is_Arrow) {
              Dafny.ISequence<DAST._IType> _1399___mcc_h787 = _source28.dtor_args;
              DAST._IType _1400___mcc_h788 = _source28.dtor_result;
              DAST._IType _source50 = _572___mcc_h284;
              if (_source50.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1401___mcc_h795 = _source50.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1402___mcc_h796 = _source50.dtor_typeArgs;
                DAST._IResolvedType _1403___mcc_h797 = _source50.dtor_resolved;
                DAST._IResolvedType _source51 = _1403___mcc_h797;
                if (_source51.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1404___mcc_h801 = _source51.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1405_recursiveGen;
                    bool _1406_recOwned;
                    bool _1407_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1408_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out815;
                    bool _out816;
                    bool _out817;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out818;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out815, out _out816, out _out817, out _out818);
                    _1405_recursiveGen = _out815;
                    _1406_recOwned = _out816;
                    _1407_recErased = _out817;
                    _1408_recIdents = _out818;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1405_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1406_recOwned;
                    isErased = _1407_recErased;
                    readIdents = _1408_recIdents;
                  }
                } else if (_source51.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1409___mcc_h803 = _source51.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1410_recursiveGen;
                    bool _1411_recOwned;
                    bool _1412_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1413_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out819;
                    bool _out820;
                    bool _out821;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out822;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out819, out _out820, out _out821, out _out822);
                    _1410_recursiveGen = _out819;
                    _1411_recOwned = _out820;
                    _1412_recErased = _out821;
                    _1413_recIdents = _out822;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1410_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1411_recOwned;
                    isErased = _1412_recErased;
                    readIdents = _1413_recIdents;
                  }
                } else {
                  DAST._IType _1414___mcc_h805 = _source51.dtor_Newtype_a0;
                  DAST._IType _1415_b = _1414___mcc_h805;
                  {
                    if (object.Equals(_565_fromTpe, _1415_b)) {
                      Dafny.ISequence<Dafny.Rune> _1416_recursiveGen;
                      bool _1417_recOwned;
                      bool _1418_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1419_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out823;
                      bool _out824;
                      bool _out825;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out826;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out823, out _out824, out _out825, out _out826);
                      _1416_recursiveGen = _out823;
                      _1417_recOwned = _out824;
                      _1418_recErased = _out825;
                      _1419_recIdents = _out826;
                      Dafny.ISequence<Dafny.Rune> _1420_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out827;
                      _out827 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                      _1420_rhsType = _out827;
                      Dafny.ISequence<Dafny.Rune> _1421_uneraseFn;
                      _1421_uneraseFn = ((_1417_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1420_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1421_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1416_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1417_recOwned;
                      isErased = false;
                      readIdents = _1419_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out828;
                      bool _out829;
                      bool _out830;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out831;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _1415_b), _1415_b, _564_toTpe), selfIdent, @params, mustOwn, out _out828, out _out829, out _out830, out _out831);
                      s = _out828;
                      isOwned = _out829;
                      isErased = _out830;
                      readIdents = _out831;
                    }
                  }
                }
              } else if (_source50.is_Nullable) {
                DAST._IType _1422___mcc_h807 = _source50.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1423_recursiveGen;
                  bool _1424_recOwned;
                  bool _1425_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1426_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out832;
                  bool _out833;
                  bool _out834;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out835;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out832, out _out833, out _out834, out _out835);
                  _1423_recursiveGen = _out832;
                  _1424_recOwned = _out833;
                  _1425_recErased = _out834;
                  _1426_recIdents = _out835;
                  if (!(_1424_recOwned)) {
                    _1423_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1423_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1423_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1425_recErased;
                  readIdents = _1426_recIdents;
                }
              } else if (_source50.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1427___mcc_h809 = _source50.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1428_recursiveGen;
                  bool _1429_recOwned;
                  bool _1430_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1431_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out836;
                  bool _out837;
                  bool _out838;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out839;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out836, out _out837, out _out838, out _out839);
                  _1428_recursiveGen = _out836;
                  _1429_recOwned = _out837;
                  _1430_recErased = _out838;
                  _1431_recIdents = _out839;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1428_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1429_recOwned;
                  isErased = _1430_recErased;
                  readIdents = _1431_recIdents;
                }
              } else if (_source50.is_Array) {
                DAST._IType _1432___mcc_h811 = _source50.dtor_element;
                BigInteger _1433___mcc_h812 = _source50.dtor_dims;
                {
                  Dafny.ISequence<Dafny.Rune> _1434_recursiveGen;
                  bool _1435_recOwned;
                  bool _1436_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1437_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out840;
                  bool _out841;
                  bool _out842;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out843;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out840, out _out841, out _out842, out _out843);
                  _1434_recursiveGen = _out840;
                  _1435_recOwned = _out841;
                  _1436_recErased = _out842;
                  _1437_recIdents = _out843;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1434_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1435_recOwned;
                  isErased = _1436_recErased;
                  readIdents = _1437_recIdents;
                }
              } else if (_source50.is_Seq) {
                DAST._IType _1438___mcc_h815 = _source50.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1439_recursiveGen;
                  bool _1440_recOwned;
                  bool _1441_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1442_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out844;
                  bool _out845;
                  bool _out846;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out847;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out844, out _out845, out _out846, out _out847);
                  _1439_recursiveGen = _out844;
                  _1440_recOwned = _out845;
                  _1441_recErased = _out846;
                  _1442_recIdents = _out847;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1439_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1440_recOwned;
                  isErased = _1441_recErased;
                  readIdents = _1442_recIdents;
                }
              } else if (_source50.is_Set) {
                DAST._IType _1443___mcc_h817 = _source50.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1444_recursiveGen;
                  bool _1445_recOwned;
                  bool _1446_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1447_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out848;
                  bool _out849;
                  bool _out850;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out851;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out848, out _out849, out _out850, out _out851);
                  _1444_recursiveGen = _out848;
                  _1445_recOwned = _out849;
                  _1446_recErased = _out850;
                  _1447_recIdents = _out851;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1444_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1445_recOwned;
                  isErased = _1446_recErased;
                  readIdents = _1447_recIdents;
                }
              } else if (_source50.is_Multiset) {
                DAST._IType _1448___mcc_h819 = _source50.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1449_recursiveGen;
                  bool _1450_recOwned;
                  bool _1451_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1452_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out852;
                  bool _out853;
                  bool _out854;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out855;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out852, out _out853, out _out854, out _out855);
                  _1449_recursiveGen = _out852;
                  _1450_recOwned = _out853;
                  _1451_recErased = _out854;
                  _1452_recIdents = _out855;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1449_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1450_recOwned;
                  isErased = _1451_recErased;
                  readIdents = _1452_recIdents;
                }
              } else if (_source50.is_Map) {
                DAST._IType _1453___mcc_h821 = _source50.dtor_key;
                DAST._IType _1454___mcc_h822 = _source50.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1455_recursiveGen;
                  bool _1456_recOwned;
                  bool _1457_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1458_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out856;
                  bool _out857;
                  bool _out858;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out859;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out856, out _out857, out _out858, out _out859);
                  _1455_recursiveGen = _out856;
                  _1456_recOwned = _out857;
                  _1457_recErased = _out858;
                  _1458_recIdents = _out859;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1455_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1456_recOwned;
                  isErased = _1457_recErased;
                  readIdents = _1458_recIdents;
                }
              } else if (_source50.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1459___mcc_h825 = _source50.dtor_args;
                DAST._IType _1460___mcc_h826 = _source50.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1461_recursiveGen;
                  bool _1462_recOwned;
                  bool _1463_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1464_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out860;
                  bool _out861;
                  bool _out862;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out863;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out860, out _out861, out _out862, out _out863);
                  _1461_recursiveGen = _out860;
                  _1462_recOwned = _out861;
                  _1463_recErased = _out862;
                  _1464_recIdents = _out863;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1461_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1462_recOwned;
                  isErased = _1463_recErased;
                  readIdents = _1464_recIdents;
                }
              } else if (_source50.is_Primitive) {
                DAST._IPrimitive _1465___mcc_h829 = _source50.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1466_recursiveGen;
                  bool _1467_recOwned;
                  bool _1468_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1469_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out864;
                  bool _out865;
                  bool _out866;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out867;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out864, out _out865, out _out866, out _out867);
                  _1466_recursiveGen = _out864;
                  _1467_recOwned = _out865;
                  _1468_recErased = _out866;
                  _1469_recIdents = _out867;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1466_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1467_recOwned;
                  isErased = _1468_recErased;
                  readIdents = _1469_recIdents;
                }
              } else if (_source50.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1470___mcc_h831 = _source50.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1471_recursiveGen;
                  bool _1472_recOwned;
                  bool _1473_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1474_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out868;
                  bool _out869;
                  bool _out870;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out871;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out868, out _out869, out _out870, out _out871);
                  _1471_recursiveGen = _out868;
                  _1472_recOwned = _out869;
                  _1473_recErased = _out870;
                  _1474_recIdents = _out871;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1471_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1472_recOwned;
                  isErased = _1473_recErased;
                  readIdents = _1474_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1475___mcc_h833 = _source50.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1476_recursiveGen;
                  bool _1477_recOwned;
                  bool _1478_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1479_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out872;
                  bool _out873;
                  bool _out874;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out875;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out872, out _out873, out _out874, out _out875);
                  _1476_recursiveGen = _out872;
                  _1477_recOwned = _out873;
                  _1478_recErased = _out874;
                  _1479_recIdents = _out875;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1476_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1477_recOwned;
                  isErased = _1478_recErased;
                  readIdents = _1479_recIdents;
                }
              }
            } else if (_source28.is_Primitive) {
              DAST._IPrimitive _1480___mcc_h835 = _source28.dtor_Primitive_a0;
              DAST._IPrimitive _source52 = _1480___mcc_h835;
              if (_source52.is_Int) {
                DAST._IType _source53 = _572___mcc_h284;
                if (_source53.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1481___mcc_h839 = _source53.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1482___mcc_h840 = _source53.dtor_typeArgs;
                  DAST._IResolvedType _1483___mcc_h841 = _source53.dtor_resolved;
                  DAST._IResolvedType _source54 = _1483___mcc_h841;
                  if (_source54.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1484___mcc_h845 = _source54.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1485_recursiveGen;
                      bool _1486_recOwned;
                      bool _1487_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1488_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out876;
                      bool _out877;
                      bool _out878;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out879;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out876, out _out877, out _out878, out _out879);
                      _1485_recursiveGen = _out876;
                      _1486_recOwned = _out877;
                      _1487_recErased = _out878;
                      _1488_recIdents = _out879;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1485_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1486_recOwned;
                      isErased = _1487_recErased;
                      readIdents = _1488_recIdents;
                    }
                  } else if (_source54.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1489___mcc_h847 = _source54.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1490_recursiveGen;
                      bool _1491_recOwned;
                      bool _1492_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1493_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out880;
                      bool _out881;
                      bool _out882;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out883;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out880, out _out881, out _out882, out _out883);
                      _1490_recursiveGen = _out880;
                      _1491_recOwned = _out881;
                      _1492_recErased = _out882;
                      _1493_recIdents = _out883;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1490_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1491_recOwned;
                      isErased = _1492_recErased;
                      readIdents = _1493_recIdents;
                    }
                  } else {
                    DAST._IType _1494___mcc_h849 = _source54.dtor_Newtype_a0;
                    DAST._IType _1495_b = _1494___mcc_h849;
                    {
                      if (object.Equals(_565_fromTpe, _1495_b)) {
                        Dafny.ISequence<Dafny.Rune> _1496_recursiveGen;
                        bool _1497_recOwned;
                        bool _1498_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1499_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out884;
                        bool _out885;
                        bool _out886;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out887;
                        DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out884, out _out885, out _out886, out _out887);
                        _1496_recursiveGen = _out884;
                        _1497_recOwned = _out885;
                        _1498_recErased = _out886;
                        _1499_recIdents = _out887;
                        Dafny.ISequence<Dafny.Rune> _1500_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out888;
                        _out888 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                        _1500_rhsType = _out888;
                        Dafny.ISequence<Dafny.Rune> _1501_uneraseFn;
                        _1501_uneraseFn = ((_1497_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1500_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1501_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1496_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1497_recOwned;
                        isErased = false;
                        readIdents = _1499_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out889;
                        bool _out890;
                        bool _out891;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out892;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _1495_b), _1495_b, _564_toTpe), selfIdent, @params, mustOwn, out _out889, out _out890, out _out891, out _out892);
                        s = _out889;
                        isOwned = _out890;
                        isErased = _out891;
                        readIdents = _out892;
                      }
                    }
                  }
                } else if (_source53.is_Nullable) {
                  DAST._IType _1502___mcc_h851 = _source53.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1503_recursiveGen;
                    bool _1504_recOwned;
                    bool _1505_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1506_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out893;
                    bool _out894;
                    bool _out895;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out896;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out893, out _out894, out _out895, out _out896);
                    _1503_recursiveGen = _out893;
                    _1504_recOwned = _out894;
                    _1505_recErased = _out895;
                    _1506_recIdents = _out896;
                    if (!(_1504_recOwned)) {
                      _1503_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1503_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1503_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1505_recErased;
                    readIdents = _1506_recIdents;
                  }
                } else if (_source53.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1507___mcc_h853 = _source53.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1508_recursiveGen;
                    bool _1509_recOwned;
                    bool _1510_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1511_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out897;
                    bool _out898;
                    bool _out899;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out900;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out897, out _out898, out _out899, out _out900);
                    _1508_recursiveGen = _out897;
                    _1509_recOwned = _out898;
                    _1510_recErased = _out899;
                    _1511_recIdents = _out900;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1508_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1509_recOwned;
                    isErased = _1510_recErased;
                    readIdents = _1511_recIdents;
                  }
                } else if (_source53.is_Array) {
                  DAST._IType _1512___mcc_h855 = _source53.dtor_element;
                  BigInteger _1513___mcc_h856 = _source53.dtor_dims;
                  {
                    Dafny.ISequence<Dafny.Rune> _1514_recursiveGen;
                    bool _1515_recOwned;
                    bool _1516_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1517_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out901;
                    bool _out902;
                    bool _out903;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out904;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out901, out _out902, out _out903, out _out904);
                    _1514_recursiveGen = _out901;
                    _1515_recOwned = _out902;
                    _1516_recErased = _out903;
                    _1517_recIdents = _out904;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1514_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1515_recOwned;
                    isErased = _1516_recErased;
                    readIdents = _1517_recIdents;
                  }
                } else if (_source53.is_Seq) {
                  DAST._IType _1518___mcc_h859 = _source53.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1519_recursiveGen;
                    bool _1520_recOwned;
                    bool _1521_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1522_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out905;
                    bool _out906;
                    bool _out907;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out908;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out905, out _out906, out _out907, out _out908);
                    _1519_recursiveGen = _out905;
                    _1520_recOwned = _out906;
                    _1521_recErased = _out907;
                    _1522_recIdents = _out908;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1519_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1520_recOwned;
                    isErased = _1521_recErased;
                    readIdents = _1522_recIdents;
                  }
                } else if (_source53.is_Set) {
                  DAST._IType _1523___mcc_h861 = _source53.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1524_recursiveGen;
                    bool _1525_recOwned;
                    bool _1526_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1527_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out909;
                    bool _out910;
                    bool _out911;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out912;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out909, out _out910, out _out911, out _out912);
                    _1524_recursiveGen = _out909;
                    _1525_recOwned = _out910;
                    _1526_recErased = _out911;
                    _1527_recIdents = _out912;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1524_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1525_recOwned;
                    isErased = _1526_recErased;
                    readIdents = _1527_recIdents;
                  }
                } else if (_source53.is_Multiset) {
                  DAST._IType _1528___mcc_h863 = _source53.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1529_recursiveGen;
                    bool _1530_recOwned;
                    bool _1531_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1532_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out913;
                    bool _out914;
                    bool _out915;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out916;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out913, out _out914, out _out915, out _out916);
                    _1529_recursiveGen = _out913;
                    _1530_recOwned = _out914;
                    _1531_recErased = _out915;
                    _1532_recIdents = _out916;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1529_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1530_recOwned;
                    isErased = _1531_recErased;
                    readIdents = _1532_recIdents;
                  }
                } else if (_source53.is_Map) {
                  DAST._IType _1533___mcc_h865 = _source53.dtor_key;
                  DAST._IType _1534___mcc_h866 = _source53.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1535_recursiveGen;
                    bool _1536_recOwned;
                    bool _1537_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1538_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out917;
                    bool _out918;
                    bool _out919;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out920;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out917, out _out918, out _out919, out _out920);
                    _1535_recursiveGen = _out917;
                    _1536_recOwned = _out918;
                    _1537_recErased = _out919;
                    _1538_recIdents = _out920;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1535_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1536_recOwned;
                    isErased = _1537_recErased;
                    readIdents = _1538_recIdents;
                  }
                } else if (_source53.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1539___mcc_h869 = _source53.dtor_args;
                  DAST._IType _1540___mcc_h870 = _source53.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1541_recursiveGen;
                    bool _1542_recOwned;
                    bool _1543_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1544_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out921;
                    bool _out922;
                    bool _out923;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out924;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out921, out _out922, out _out923, out _out924);
                    _1541_recursiveGen = _out921;
                    _1542_recOwned = _out922;
                    _1543_recErased = _out923;
                    _1544_recIdents = _out924;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1541_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1542_recOwned;
                    isErased = _1543_recErased;
                    readIdents = _1544_recIdents;
                  }
                } else if (_source53.is_Primitive) {
                  DAST._IPrimitive _1545___mcc_h873 = _source53.dtor_Primitive_a0;
                  DAST._IPrimitive _source55 = _1545___mcc_h873;
                  if (_source55.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1546_recursiveGen;
                      bool _1547_recOwned;
                      bool _1548_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1549_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out925;
                      bool _out926;
                      bool _out927;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out928;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out925, out _out926, out _out927, out _out928);
                      _1546_recursiveGen = _out925;
                      _1547_recOwned = _out926;
                      _1548_recErased = _out927;
                      _1549_recIdents = _out928;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1546_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1547_recOwned;
                      isErased = _1548_recErased;
                      readIdents = _1549_recIdents;
                    }
                  } else if (_source55.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1550_recursiveGen;
                      bool _1551___v48;
                      bool _1552___v49;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1553_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out929;
                      bool _out930;
                      bool _out931;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out932;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, true, out _out929, out _out930, out _out931, out _out932);
                      _1550_recursiveGen = _out929;
                      _1551___v48 = _out930;
                      _1552___v49 = _out931;
                      _1553_recIdents = _out932;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), _1550_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1553_recIdents;
                    }
                  } else if (_source55.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1554_recursiveGen;
                      bool _1555_recOwned;
                      bool _1556_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1557_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out933;
                      bool _out934;
                      bool _out935;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out936;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out933, out _out934, out _out935, out _out936);
                      _1554_recursiveGen = _out933;
                      _1555_recOwned = _out934;
                      _1556_recErased = _out935;
                      _1557_recIdents = _out936;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1554_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1555_recOwned;
                      isErased = _1556_recErased;
                      readIdents = _1557_recIdents;
                    }
                  } else if (_source55.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1558_recursiveGen;
                      bool _1559_recOwned;
                      bool _1560_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1561_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out937;
                      bool _out938;
                      bool _out939;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out940;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out937, out _out938, out _out939, out _out940);
                      _1558_recursiveGen = _out937;
                      _1559_recOwned = _out938;
                      _1560_recErased = _out939;
                      _1561_recIdents = _out940;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1558_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1559_recOwned;
                      isErased = _1560_recErased;
                      readIdents = _1561_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1562_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out941;
                      _out941 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                      _1562_rhsType = _out941;
                      Dafny.ISequence<Dafny.Rune> _1563_recursiveGen;
                      bool _1564___v58;
                      bool _1565___v59;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1566_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out942;
                      bool _out943;
                      bool _out944;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out945;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, true, out _out942, out _out943, out _out944, out _out945);
                      _1563_recursiveGen = _out942;
                      _1564___v58 = _out943;
                      _1565___v59 = _out944;
                      _1566_recIdents = _out945;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), _1563_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1566_recIdents;
                    }
                  }
                } else if (_source53.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1567___mcc_h875 = _source53.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1568_rhsType;
                    Dafny.ISequence<Dafny.Rune> _out946;
                    _out946 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                    _1568_rhsType = _out946;
                    Dafny.ISequence<Dafny.Rune> _1569_recursiveGen;
                    bool _1570___v53;
                    bool _1571___v54;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1572_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out947;
                    bool _out948;
                    bool _out949;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out950;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, true, out _out947, out _out948, out _out949, out _out950);
                    _1569_recursiveGen = _out947;
                    _1570___v53 = _out948;
                    _1571___v54 = _out949;
                    _1572_recIdents = _out950;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1568_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), _1569_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"));
                    isOwned = true;
                    isErased = true;
                    readIdents = _1572_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1573___mcc_h877 = _source53.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1574_recursiveGen;
                    bool _1575_recOwned;
                    bool _1576_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1577_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out951;
                    bool _out952;
                    bool _out953;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out954;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out951, out _out952, out _out953, out _out954);
                    _1574_recursiveGen = _out951;
                    _1575_recOwned = _out952;
                    _1576_recErased = _out953;
                    _1577_recIdents = _out954;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1574_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1575_recOwned;
                    isErased = _1576_recErased;
                    readIdents = _1577_recIdents;
                  }
                }
              } else if (_source52.is_Real) {
                DAST._IType _source56 = _572___mcc_h284;
                if (_source56.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1578___mcc_h879 = _source56.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1579___mcc_h880 = _source56.dtor_typeArgs;
                  DAST._IResolvedType _1580___mcc_h881 = _source56.dtor_resolved;
                  DAST._IResolvedType _source57 = _1580___mcc_h881;
                  if (_source57.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1581___mcc_h885 = _source57.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1582_recursiveGen;
                      bool _1583_recOwned;
                      bool _1584_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1585_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out955;
                      bool _out956;
                      bool _out957;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out958;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out955, out _out956, out _out957, out _out958);
                      _1582_recursiveGen = _out955;
                      _1583_recOwned = _out956;
                      _1584_recErased = _out957;
                      _1585_recIdents = _out958;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1582_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1583_recOwned;
                      isErased = _1584_recErased;
                      readIdents = _1585_recIdents;
                    }
                  } else if (_source57.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1586___mcc_h887 = _source57.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1587_recursiveGen;
                      bool _1588_recOwned;
                      bool _1589_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1590_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out959;
                      bool _out960;
                      bool _out961;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out962;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out959, out _out960, out _out961, out _out962);
                      _1587_recursiveGen = _out959;
                      _1588_recOwned = _out960;
                      _1589_recErased = _out961;
                      _1590_recIdents = _out962;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1587_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1588_recOwned;
                      isErased = _1589_recErased;
                      readIdents = _1590_recIdents;
                    }
                  } else {
                    DAST._IType _1591___mcc_h889 = _source57.dtor_Newtype_a0;
                    DAST._IType _1592_b = _1591___mcc_h889;
                    {
                      if (object.Equals(_565_fromTpe, _1592_b)) {
                        Dafny.ISequence<Dafny.Rune> _1593_recursiveGen;
                        bool _1594_recOwned;
                        bool _1595_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1596_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out963;
                        bool _out964;
                        bool _out965;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out966;
                        DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out963, out _out964, out _out965, out _out966);
                        _1593_recursiveGen = _out963;
                        _1594_recOwned = _out964;
                        _1595_recErased = _out965;
                        _1596_recIdents = _out966;
                        Dafny.ISequence<Dafny.Rune> _1597_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out967;
                        _out967 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                        _1597_rhsType = _out967;
                        Dafny.ISequence<Dafny.Rune> _1598_uneraseFn;
                        _1598_uneraseFn = ((_1594_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1597_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1598_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1593_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1594_recOwned;
                        isErased = false;
                        readIdents = _1596_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out968;
                        bool _out969;
                        bool _out970;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out971;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _1592_b), _1592_b, _564_toTpe), selfIdent, @params, mustOwn, out _out968, out _out969, out _out970, out _out971);
                        s = _out968;
                        isOwned = _out969;
                        isErased = _out970;
                        readIdents = _out971;
                      }
                    }
                  }
                } else if (_source56.is_Nullable) {
                  DAST._IType _1599___mcc_h891 = _source56.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1600_recursiveGen;
                    bool _1601_recOwned;
                    bool _1602_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1603_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out972;
                    bool _out973;
                    bool _out974;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out975;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out972, out _out973, out _out974, out _out975);
                    _1600_recursiveGen = _out972;
                    _1601_recOwned = _out973;
                    _1602_recErased = _out974;
                    _1603_recIdents = _out975;
                    if (!(_1601_recOwned)) {
                      _1600_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1600_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1600_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1602_recErased;
                    readIdents = _1603_recIdents;
                  }
                } else if (_source56.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1604___mcc_h893 = _source56.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1605_recursiveGen;
                    bool _1606_recOwned;
                    bool _1607_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1608_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out976;
                    bool _out977;
                    bool _out978;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out979;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out976, out _out977, out _out978, out _out979);
                    _1605_recursiveGen = _out976;
                    _1606_recOwned = _out977;
                    _1607_recErased = _out978;
                    _1608_recIdents = _out979;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1605_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1606_recOwned;
                    isErased = _1607_recErased;
                    readIdents = _1608_recIdents;
                  }
                } else if (_source56.is_Array) {
                  DAST._IType _1609___mcc_h895 = _source56.dtor_element;
                  BigInteger _1610___mcc_h896 = _source56.dtor_dims;
                  {
                    Dafny.ISequence<Dafny.Rune> _1611_recursiveGen;
                    bool _1612_recOwned;
                    bool _1613_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1614_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out980;
                    bool _out981;
                    bool _out982;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out983;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out980, out _out981, out _out982, out _out983);
                    _1611_recursiveGen = _out980;
                    _1612_recOwned = _out981;
                    _1613_recErased = _out982;
                    _1614_recIdents = _out983;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1611_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1612_recOwned;
                    isErased = _1613_recErased;
                    readIdents = _1614_recIdents;
                  }
                } else if (_source56.is_Seq) {
                  DAST._IType _1615___mcc_h899 = _source56.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1616_recursiveGen;
                    bool _1617_recOwned;
                    bool _1618_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1619_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out984;
                    bool _out985;
                    bool _out986;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out987;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out984, out _out985, out _out986, out _out987);
                    _1616_recursiveGen = _out984;
                    _1617_recOwned = _out985;
                    _1618_recErased = _out986;
                    _1619_recIdents = _out987;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1616_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1617_recOwned;
                    isErased = _1618_recErased;
                    readIdents = _1619_recIdents;
                  }
                } else if (_source56.is_Set) {
                  DAST._IType _1620___mcc_h901 = _source56.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1621_recursiveGen;
                    bool _1622_recOwned;
                    bool _1623_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1624_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out988;
                    bool _out989;
                    bool _out990;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out991;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out988, out _out989, out _out990, out _out991);
                    _1621_recursiveGen = _out988;
                    _1622_recOwned = _out989;
                    _1623_recErased = _out990;
                    _1624_recIdents = _out991;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1621_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1622_recOwned;
                    isErased = _1623_recErased;
                    readIdents = _1624_recIdents;
                  }
                } else if (_source56.is_Multiset) {
                  DAST._IType _1625___mcc_h903 = _source56.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1626_recursiveGen;
                    bool _1627_recOwned;
                    bool _1628_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1629_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out992;
                    bool _out993;
                    bool _out994;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out995;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out992, out _out993, out _out994, out _out995);
                    _1626_recursiveGen = _out992;
                    _1627_recOwned = _out993;
                    _1628_recErased = _out994;
                    _1629_recIdents = _out995;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1626_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1627_recOwned;
                    isErased = _1628_recErased;
                    readIdents = _1629_recIdents;
                  }
                } else if (_source56.is_Map) {
                  DAST._IType _1630___mcc_h905 = _source56.dtor_key;
                  DAST._IType _1631___mcc_h906 = _source56.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1632_recursiveGen;
                    bool _1633_recOwned;
                    bool _1634_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1635_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out996;
                    bool _out997;
                    bool _out998;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out999;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out996, out _out997, out _out998, out _out999);
                    _1632_recursiveGen = _out996;
                    _1633_recOwned = _out997;
                    _1634_recErased = _out998;
                    _1635_recIdents = _out999;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1632_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1633_recOwned;
                    isErased = _1634_recErased;
                    readIdents = _1635_recIdents;
                  }
                } else if (_source56.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1636___mcc_h909 = _source56.dtor_args;
                  DAST._IType _1637___mcc_h910 = _source56.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1638_recursiveGen;
                    bool _1639_recOwned;
                    bool _1640_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1641_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1000;
                    bool _out1001;
                    bool _out1002;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1003;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1000, out _out1001, out _out1002, out _out1003);
                    _1638_recursiveGen = _out1000;
                    _1639_recOwned = _out1001;
                    _1640_recErased = _out1002;
                    _1641_recIdents = _out1003;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1638_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1639_recOwned;
                    isErased = _1640_recErased;
                    readIdents = _1641_recIdents;
                  }
                } else if (_source56.is_Primitive) {
                  DAST._IPrimitive _1642___mcc_h913 = _source56.dtor_Primitive_a0;
                  DAST._IPrimitive _source58 = _1642___mcc_h913;
                  if (_source58.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1643_recursiveGen;
                      bool _1644___v50;
                      bool _1645___v51;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1646_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1004;
                      bool _out1005;
                      bool _out1006;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1007;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, false, out _out1004, out _out1005, out _out1006, out _out1007);
                      _1643_recursiveGen = _out1004;
                      _1644___v50 = _out1005;
                      _1645___v51 = _out1006;
                      _1646_recIdents = _out1007;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), _1643_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1646_recIdents;
                    }
                  } else if (_source58.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1647_recursiveGen;
                      bool _1648_recOwned;
                      bool _1649_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1650_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1008;
                      bool _out1009;
                      bool _out1010;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1011;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1008, out _out1009, out _out1010, out _out1011);
                      _1647_recursiveGen = _out1008;
                      _1648_recOwned = _out1009;
                      _1649_recErased = _out1010;
                      _1650_recIdents = _out1011;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1647_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1648_recOwned;
                      isErased = _1649_recErased;
                      readIdents = _1650_recIdents;
                    }
                  } else if (_source58.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1651_recursiveGen;
                      bool _1652_recOwned;
                      bool _1653_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1654_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1012;
                      bool _out1013;
                      bool _out1014;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1015;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1012, out _out1013, out _out1014, out _out1015);
                      _1651_recursiveGen = _out1012;
                      _1652_recOwned = _out1013;
                      _1653_recErased = _out1014;
                      _1654_recIdents = _out1015;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1651_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1652_recOwned;
                      isErased = _1653_recErased;
                      readIdents = _1654_recIdents;
                    }
                  } else if (_source58.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1655_recursiveGen;
                      bool _1656_recOwned;
                      bool _1657_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1658_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1016;
                      bool _out1017;
                      bool _out1018;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1019;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1016, out _out1017, out _out1018, out _out1019);
                      _1655_recursiveGen = _out1016;
                      _1656_recOwned = _out1017;
                      _1657_recErased = _out1018;
                      _1658_recIdents = _out1019;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1655_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1656_recOwned;
                      isErased = _1657_recErased;
                      readIdents = _1658_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1659_recursiveGen;
                      bool _1660_recOwned;
                      bool _1661_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1662_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1020;
                      bool _out1021;
                      bool _out1022;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1023;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1020, out _out1021, out _out1022, out _out1023);
                      _1659_recursiveGen = _out1020;
                      _1660_recOwned = _out1021;
                      _1661_recErased = _out1022;
                      _1662_recIdents = _out1023;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1659_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1660_recOwned;
                      isErased = _1661_recErased;
                      readIdents = _1662_recIdents;
                    }
                  }
                } else if (_source56.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1663___mcc_h915 = _source56.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1664_recursiveGen;
                    bool _1665_recOwned;
                    bool _1666_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1667_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1024;
                    bool _out1025;
                    bool _out1026;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1027;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1024, out _out1025, out _out1026, out _out1027);
                    _1664_recursiveGen = _out1024;
                    _1665_recOwned = _out1025;
                    _1666_recErased = _out1026;
                    _1667_recIdents = _out1027;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1664_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1665_recOwned;
                    isErased = _1666_recErased;
                    readIdents = _1667_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1668___mcc_h917 = _source56.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1669_recursiveGen;
                    bool _1670_recOwned;
                    bool _1671_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1672_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1028;
                    bool _out1029;
                    bool _out1030;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1031;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1028, out _out1029, out _out1030, out _out1031);
                    _1669_recursiveGen = _out1028;
                    _1670_recOwned = _out1029;
                    _1671_recErased = _out1030;
                    _1672_recIdents = _out1031;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1669_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1670_recOwned;
                    isErased = _1671_recErased;
                    readIdents = _1672_recIdents;
                  }
                }
              } else if (_source52.is_String) {
                DAST._IType _source59 = _572___mcc_h284;
                if (_source59.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1673___mcc_h919 = _source59.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1674___mcc_h920 = _source59.dtor_typeArgs;
                  DAST._IResolvedType _1675___mcc_h921 = _source59.dtor_resolved;
                  DAST._IResolvedType _source60 = _1675___mcc_h921;
                  if (_source60.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1676___mcc_h925 = _source60.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1677_recursiveGen;
                      bool _1678_recOwned;
                      bool _1679_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1680_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1032;
                      bool _out1033;
                      bool _out1034;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1035;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1032, out _out1033, out _out1034, out _out1035);
                      _1677_recursiveGen = _out1032;
                      _1678_recOwned = _out1033;
                      _1679_recErased = _out1034;
                      _1680_recIdents = _out1035;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1677_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1678_recOwned;
                      isErased = _1679_recErased;
                      readIdents = _1680_recIdents;
                    }
                  } else if (_source60.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1681___mcc_h927 = _source60.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1682_recursiveGen;
                      bool _1683_recOwned;
                      bool _1684_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1685_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1036;
                      bool _out1037;
                      bool _out1038;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1039;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1036, out _out1037, out _out1038, out _out1039);
                      _1682_recursiveGen = _out1036;
                      _1683_recOwned = _out1037;
                      _1684_recErased = _out1038;
                      _1685_recIdents = _out1039;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1682_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1683_recOwned;
                      isErased = _1684_recErased;
                      readIdents = _1685_recIdents;
                    }
                  } else {
                    DAST._IType _1686___mcc_h929 = _source60.dtor_Newtype_a0;
                    DAST._IType _1687_b = _1686___mcc_h929;
                    {
                      if (object.Equals(_565_fromTpe, _1687_b)) {
                        Dafny.ISequence<Dafny.Rune> _1688_recursiveGen;
                        bool _1689_recOwned;
                        bool _1690_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1691_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1040;
                        bool _out1041;
                        bool _out1042;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1043;
                        DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1040, out _out1041, out _out1042, out _out1043);
                        _1688_recursiveGen = _out1040;
                        _1689_recOwned = _out1041;
                        _1690_recErased = _out1042;
                        _1691_recIdents = _out1043;
                        Dafny.ISequence<Dafny.Rune> _1692_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1044;
                        _out1044 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                        _1692_rhsType = _out1044;
                        Dafny.ISequence<Dafny.Rune> _1693_uneraseFn;
                        _1693_uneraseFn = ((_1689_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1692_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1693_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1688_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1689_recOwned;
                        isErased = false;
                        readIdents = _1691_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1045;
                        bool _out1046;
                        bool _out1047;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1048;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _1687_b), _1687_b, _564_toTpe), selfIdent, @params, mustOwn, out _out1045, out _out1046, out _out1047, out _out1048);
                        s = _out1045;
                        isOwned = _out1046;
                        isErased = _out1047;
                        readIdents = _out1048;
                      }
                    }
                  }
                } else if (_source59.is_Nullable) {
                  DAST._IType _1694___mcc_h931 = _source59.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1695_recursiveGen;
                    bool _1696_recOwned;
                    bool _1697_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1698_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1049;
                    bool _out1050;
                    bool _out1051;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1052;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1049, out _out1050, out _out1051, out _out1052);
                    _1695_recursiveGen = _out1049;
                    _1696_recOwned = _out1050;
                    _1697_recErased = _out1051;
                    _1698_recIdents = _out1052;
                    if (!(_1696_recOwned)) {
                      _1695_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1695_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1695_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1697_recErased;
                    readIdents = _1698_recIdents;
                  }
                } else if (_source59.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1699___mcc_h933 = _source59.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1700_recursiveGen;
                    bool _1701_recOwned;
                    bool _1702_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1703_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1053;
                    bool _out1054;
                    bool _out1055;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1056;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1053, out _out1054, out _out1055, out _out1056);
                    _1700_recursiveGen = _out1053;
                    _1701_recOwned = _out1054;
                    _1702_recErased = _out1055;
                    _1703_recIdents = _out1056;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1700_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1701_recOwned;
                    isErased = _1702_recErased;
                    readIdents = _1703_recIdents;
                  }
                } else if (_source59.is_Array) {
                  DAST._IType _1704___mcc_h935 = _source59.dtor_element;
                  BigInteger _1705___mcc_h936 = _source59.dtor_dims;
                  {
                    Dafny.ISequence<Dafny.Rune> _1706_recursiveGen;
                    bool _1707_recOwned;
                    bool _1708_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1709_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1057;
                    bool _out1058;
                    bool _out1059;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1060;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1057, out _out1058, out _out1059, out _out1060);
                    _1706_recursiveGen = _out1057;
                    _1707_recOwned = _out1058;
                    _1708_recErased = _out1059;
                    _1709_recIdents = _out1060;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1706_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1707_recOwned;
                    isErased = _1708_recErased;
                    readIdents = _1709_recIdents;
                  }
                } else if (_source59.is_Seq) {
                  DAST._IType _1710___mcc_h939 = _source59.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1711_recursiveGen;
                    bool _1712_recOwned;
                    bool _1713_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1714_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1061;
                    bool _out1062;
                    bool _out1063;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1064;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1061, out _out1062, out _out1063, out _out1064);
                    _1711_recursiveGen = _out1061;
                    _1712_recOwned = _out1062;
                    _1713_recErased = _out1063;
                    _1714_recIdents = _out1064;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1711_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1712_recOwned;
                    isErased = _1713_recErased;
                    readIdents = _1714_recIdents;
                  }
                } else if (_source59.is_Set) {
                  DAST._IType _1715___mcc_h941 = _source59.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1716_recursiveGen;
                    bool _1717_recOwned;
                    bool _1718_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1719_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1065;
                    bool _out1066;
                    bool _out1067;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1068;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1065, out _out1066, out _out1067, out _out1068);
                    _1716_recursiveGen = _out1065;
                    _1717_recOwned = _out1066;
                    _1718_recErased = _out1067;
                    _1719_recIdents = _out1068;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1716_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1717_recOwned;
                    isErased = _1718_recErased;
                    readIdents = _1719_recIdents;
                  }
                } else if (_source59.is_Multiset) {
                  DAST._IType _1720___mcc_h943 = _source59.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1721_recursiveGen;
                    bool _1722_recOwned;
                    bool _1723_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1724_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1069;
                    bool _out1070;
                    bool _out1071;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1072;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1069, out _out1070, out _out1071, out _out1072);
                    _1721_recursiveGen = _out1069;
                    _1722_recOwned = _out1070;
                    _1723_recErased = _out1071;
                    _1724_recIdents = _out1072;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1721_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1722_recOwned;
                    isErased = _1723_recErased;
                    readIdents = _1724_recIdents;
                  }
                } else if (_source59.is_Map) {
                  DAST._IType _1725___mcc_h945 = _source59.dtor_key;
                  DAST._IType _1726___mcc_h946 = _source59.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1727_recursiveGen;
                    bool _1728_recOwned;
                    bool _1729_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1730_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1073;
                    bool _out1074;
                    bool _out1075;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1076;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1073, out _out1074, out _out1075, out _out1076);
                    _1727_recursiveGen = _out1073;
                    _1728_recOwned = _out1074;
                    _1729_recErased = _out1075;
                    _1730_recIdents = _out1076;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1727_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1728_recOwned;
                    isErased = _1729_recErased;
                    readIdents = _1730_recIdents;
                  }
                } else if (_source59.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1731___mcc_h949 = _source59.dtor_args;
                  DAST._IType _1732___mcc_h950 = _source59.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1733_recursiveGen;
                    bool _1734_recOwned;
                    bool _1735_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1736_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1077;
                    bool _out1078;
                    bool _out1079;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1080;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1077, out _out1078, out _out1079, out _out1080);
                    _1733_recursiveGen = _out1077;
                    _1734_recOwned = _out1078;
                    _1735_recErased = _out1079;
                    _1736_recIdents = _out1080;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1733_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1734_recOwned;
                    isErased = _1735_recErased;
                    readIdents = _1736_recIdents;
                  }
                } else if (_source59.is_Primitive) {
                  DAST._IPrimitive _1737___mcc_h953 = _source59.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1738_recursiveGen;
                    bool _1739_recOwned;
                    bool _1740_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1741_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1081;
                    bool _out1082;
                    bool _out1083;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1084;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1081, out _out1082, out _out1083, out _out1084);
                    _1738_recursiveGen = _out1081;
                    _1739_recOwned = _out1082;
                    _1740_recErased = _out1083;
                    _1741_recIdents = _out1084;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1738_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1739_recOwned;
                    isErased = _1740_recErased;
                    readIdents = _1741_recIdents;
                  }
                } else if (_source59.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1742___mcc_h955 = _source59.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1743_recursiveGen;
                    bool _1744_recOwned;
                    bool _1745_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1746_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1085;
                    bool _out1086;
                    bool _out1087;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1088;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1085, out _out1086, out _out1087, out _out1088);
                    _1743_recursiveGen = _out1085;
                    _1744_recOwned = _out1086;
                    _1745_recErased = _out1087;
                    _1746_recIdents = _out1088;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1743_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1744_recOwned;
                    isErased = _1745_recErased;
                    readIdents = _1746_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1747___mcc_h957 = _source59.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1748_recursiveGen;
                    bool _1749_recOwned;
                    bool _1750_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1751_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1089;
                    bool _out1090;
                    bool _out1091;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1092;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1089, out _out1090, out _out1091, out _out1092);
                    _1748_recursiveGen = _out1089;
                    _1749_recOwned = _out1090;
                    _1750_recErased = _out1091;
                    _1751_recIdents = _out1092;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1748_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1749_recOwned;
                    isErased = _1750_recErased;
                    readIdents = _1751_recIdents;
                  }
                }
              } else if (_source52.is_Bool) {
                DAST._IType _source61 = _572___mcc_h284;
                if (_source61.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1752___mcc_h959 = _source61.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1753___mcc_h960 = _source61.dtor_typeArgs;
                  DAST._IResolvedType _1754___mcc_h961 = _source61.dtor_resolved;
                  DAST._IResolvedType _source62 = _1754___mcc_h961;
                  if (_source62.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1755___mcc_h965 = _source62.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1756_recursiveGen;
                      bool _1757_recOwned;
                      bool _1758_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1759_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1093;
                      bool _out1094;
                      bool _out1095;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1096;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1093, out _out1094, out _out1095, out _out1096);
                      _1756_recursiveGen = _out1093;
                      _1757_recOwned = _out1094;
                      _1758_recErased = _out1095;
                      _1759_recIdents = _out1096;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1756_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1757_recOwned;
                      isErased = _1758_recErased;
                      readIdents = _1759_recIdents;
                    }
                  } else if (_source62.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1760___mcc_h967 = _source62.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1761_recursiveGen;
                      bool _1762_recOwned;
                      bool _1763_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1764_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1097;
                      bool _out1098;
                      bool _out1099;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1100;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1097, out _out1098, out _out1099, out _out1100);
                      _1761_recursiveGen = _out1097;
                      _1762_recOwned = _out1098;
                      _1763_recErased = _out1099;
                      _1764_recIdents = _out1100;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1761_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1762_recOwned;
                      isErased = _1763_recErased;
                      readIdents = _1764_recIdents;
                    }
                  } else {
                    DAST._IType _1765___mcc_h969 = _source62.dtor_Newtype_a0;
                    DAST._IType _1766_b = _1765___mcc_h969;
                    {
                      if (object.Equals(_565_fromTpe, _1766_b)) {
                        Dafny.ISequence<Dafny.Rune> _1767_recursiveGen;
                        bool _1768_recOwned;
                        bool _1769_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1770_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1101;
                        bool _out1102;
                        bool _out1103;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1104;
                        DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1101, out _out1102, out _out1103, out _out1104);
                        _1767_recursiveGen = _out1101;
                        _1768_recOwned = _out1102;
                        _1769_recErased = _out1103;
                        _1770_recIdents = _out1104;
                        Dafny.ISequence<Dafny.Rune> _1771_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1105;
                        _out1105 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                        _1771_rhsType = _out1105;
                        Dafny.ISequence<Dafny.Rune> _1772_uneraseFn;
                        _1772_uneraseFn = ((_1768_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1771_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1772_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1767_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1768_recOwned;
                        isErased = false;
                        readIdents = _1770_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1106;
                        bool _out1107;
                        bool _out1108;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1109;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _1766_b), _1766_b, _564_toTpe), selfIdent, @params, mustOwn, out _out1106, out _out1107, out _out1108, out _out1109);
                        s = _out1106;
                        isOwned = _out1107;
                        isErased = _out1108;
                        readIdents = _out1109;
                      }
                    }
                  }
                } else if (_source61.is_Nullable) {
                  DAST._IType _1773___mcc_h971 = _source61.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1774_recursiveGen;
                    bool _1775_recOwned;
                    bool _1776_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1777_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1110;
                    bool _out1111;
                    bool _out1112;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1113;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1110, out _out1111, out _out1112, out _out1113);
                    _1774_recursiveGen = _out1110;
                    _1775_recOwned = _out1111;
                    _1776_recErased = _out1112;
                    _1777_recIdents = _out1113;
                    if (!(_1775_recOwned)) {
                      _1774_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1774_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1774_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1776_recErased;
                    readIdents = _1777_recIdents;
                  }
                } else if (_source61.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1778___mcc_h973 = _source61.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1779_recursiveGen;
                    bool _1780_recOwned;
                    bool _1781_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1782_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1114;
                    bool _out1115;
                    bool _out1116;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1117;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1114, out _out1115, out _out1116, out _out1117);
                    _1779_recursiveGen = _out1114;
                    _1780_recOwned = _out1115;
                    _1781_recErased = _out1116;
                    _1782_recIdents = _out1117;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1779_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1780_recOwned;
                    isErased = _1781_recErased;
                    readIdents = _1782_recIdents;
                  }
                } else if (_source61.is_Array) {
                  DAST._IType _1783___mcc_h975 = _source61.dtor_element;
                  BigInteger _1784___mcc_h976 = _source61.dtor_dims;
                  {
                    Dafny.ISequence<Dafny.Rune> _1785_recursiveGen;
                    bool _1786_recOwned;
                    bool _1787_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1788_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1118;
                    bool _out1119;
                    bool _out1120;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1121;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1118, out _out1119, out _out1120, out _out1121);
                    _1785_recursiveGen = _out1118;
                    _1786_recOwned = _out1119;
                    _1787_recErased = _out1120;
                    _1788_recIdents = _out1121;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1785_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1786_recOwned;
                    isErased = _1787_recErased;
                    readIdents = _1788_recIdents;
                  }
                } else if (_source61.is_Seq) {
                  DAST._IType _1789___mcc_h979 = _source61.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1790_recursiveGen;
                    bool _1791_recOwned;
                    bool _1792_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1793_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1122;
                    bool _out1123;
                    bool _out1124;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1125;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1122, out _out1123, out _out1124, out _out1125);
                    _1790_recursiveGen = _out1122;
                    _1791_recOwned = _out1123;
                    _1792_recErased = _out1124;
                    _1793_recIdents = _out1125;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1790_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1791_recOwned;
                    isErased = _1792_recErased;
                    readIdents = _1793_recIdents;
                  }
                } else if (_source61.is_Set) {
                  DAST._IType _1794___mcc_h981 = _source61.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1795_recursiveGen;
                    bool _1796_recOwned;
                    bool _1797_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1798_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1126;
                    bool _out1127;
                    bool _out1128;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1129;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1126, out _out1127, out _out1128, out _out1129);
                    _1795_recursiveGen = _out1126;
                    _1796_recOwned = _out1127;
                    _1797_recErased = _out1128;
                    _1798_recIdents = _out1129;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1795_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1796_recOwned;
                    isErased = _1797_recErased;
                    readIdents = _1798_recIdents;
                  }
                } else if (_source61.is_Multiset) {
                  DAST._IType _1799___mcc_h983 = _source61.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1800_recursiveGen;
                    bool _1801_recOwned;
                    bool _1802_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1803_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1130;
                    bool _out1131;
                    bool _out1132;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1133;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1130, out _out1131, out _out1132, out _out1133);
                    _1800_recursiveGen = _out1130;
                    _1801_recOwned = _out1131;
                    _1802_recErased = _out1132;
                    _1803_recIdents = _out1133;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1800_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1801_recOwned;
                    isErased = _1802_recErased;
                    readIdents = _1803_recIdents;
                  }
                } else if (_source61.is_Map) {
                  DAST._IType _1804___mcc_h985 = _source61.dtor_key;
                  DAST._IType _1805___mcc_h986 = _source61.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1806_recursiveGen;
                    bool _1807_recOwned;
                    bool _1808_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1809_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1134;
                    bool _out1135;
                    bool _out1136;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1137;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1134, out _out1135, out _out1136, out _out1137);
                    _1806_recursiveGen = _out1134;
                    _1807_recOwned = _out1135;
                    _1808_recErased = _out1136;
                    _1809_recIdents = _out1137;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1806_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1807_recOwned;
                    isErased = _1808_recErased;
                    readIdents = _1809_recIdents;
                  }
                } else if (_source61.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1810___mcc_h989 = _source61.dtor_args;
                  DAST._IType _1811___mcc_h990 = _source61.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1812_recursiveGen;
                    bool _1813_recOwned;
                    bool _1814_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1815_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1138;
                    bool _out1139;
                    bool _out1140;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1141;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1138, out _out1139, out _out1140, out _out1141);
                    _1812_recursiveGen = _out1138;
                    _1813_recOwned = _out1139;
                    _1814_recErased = _out1140;
                    _1815_recIdents = _out1141;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1812_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1813_recOwned;
                    isErased = _1814_recErased;
                    readIdents = _1815_recIdents;
                  }
                } else if (_source61.is_Primitive) {
                  DAST._IPrimitive _1816___mcc_h993 = _source61.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1817_recursiveGen;
                    bool _1818_recOwned;
                    bool _1819_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1820_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1142;
                    bool _out1143;
                    bool _out1144;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1145;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1142, out _out1143, out _out1144, out _out1145);
                    _1817_recursiveGen = _out1142;
                    _1818_recOwned = _out1143;
                    _1819_recErased = _out1144;
                    _1820_recIdents = _out1145;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1817_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1818_recOwned;
                    isErased = _1819_recErased;
                    readIdents = _1820_recIdents;
                  }
                } else if (_source61.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1821___mcc_h995 = _source61.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1822_recursiveGen;
                    bool _1823_recOwned;
                    bool _1824_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1825_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1146;
                    bool _out1147;
                    bool _out1148;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1149;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1146, out _out1147, out _out1148, out _out1149);
                    _1822_recursiveGen = _out1146;
                    _1823_recOwned = _out1147;
                    _1824_recErased = _out1148;
                    _1825_recIdents = _out1149;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1822_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1823_recOwned;
                    isErased = _1824_recErased;
                    readIdents = _1825_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1826___mcc_h997 = _source61.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1827_recursiveGen;
                    bool _1828_recOwned;
                    bool _1829_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1830_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1150;
                    bool _out1151;
                    bool _out1152;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1153;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1150, out _out1151, out _out1152, out _out1153);
                    _1827_recursiveGen = _out1150;
                    _1828_recOwned = _out1151;
                    _1829_recErased = _out1152;
                    _1830_recIdents = _out1153;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1827_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1828_recOwned;
                    isErased = _1829_recErased;
                    readIdents = _1830_recIdents;
                  }
                }
              } else {
                DAST._IType _source63 = _572___mcc_h284;
                if (_source63.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1831___mcc_h999 = _source63.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1832___mcc_h1000 = _source63.dtor_typeArgs;
                  DAST._IResolvedType _1833___mcc_h1001 = _source63.dtor_resolved;
                  DAST._IResolvedType _source64 = _1833___mcc_h1001;
                  if (_source64.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1834___mcc_h1005 = _source64.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1835_recursiveGen;
                      bool _1836_recOwned;
                      bool _1837_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1838_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1154;
                      bool _out1155;
                      bool _out1156;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1157;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1154, out _out1155, out _out1156, out _out1157);
                      _1835_recursiveGen = _out1154;
                      _1836_recOwned = _out1155;
                      _1837_recErased = _out1156;
                      _1838_recIdents = _out1157;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1835_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1836_recOwned;
                      isErased = _1837_recErased;
                      readIdents = _1838_recIdents;
                    }
                  } else if (_source64.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1839___mcc_h1007 = _source64.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1840_recursiveGen;
                      bool _1841_recOwned;
                      bool _1842_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1843_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1158;
                      bool _out1159;
                      bool _out1160;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1161;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1158, out _out1159, out _out1160, out _out1161);
                      _1840_recursiveGen = _out1158;
                      _1841_recOwned = _out1159;
                      _1842_recErased = _out1160;
                      _1843_recIdents = _out1161;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1840_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1841_recOwned;
                      isErased = _1842_recErased;
                      readIdents = _1843_recIdents;
                    }
                  } else {
                    DAST._IType _1844___mcc_h1009 = _source64.dtor_Newtype_a0;
                    DAST._IType _1845_b = _1844___mcc_h1009;
                    {
                      if (object.Equals(_565_fromTpe, _1845_b)) {
                        Dafny.ISequence<Dafny.Rune> _1846_recursiveGen;
                        bool _1847_recOwned;
                        bool _1848_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1849_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1162;
                        bool _out1163;
                        bool _out1164;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1165;
                        DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1162, out _out1163, out _out1164, out _out1165);
                        _1846_recursiveGen = _out1162;
                        _1847_recOwned = _out1163;
                        _1848_recErased = _out1164;
                        _1849_recIdents = _out1165;
                        Dafny.ISequence<Dafny.Rune> _1850_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1166;
                        _out1166 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                        _1850_rhsType = _out1166;
                        Dafny.ISequence<Dafny.Rune> _1851_uneraseFn;
                        _1851_uneraseFn = ((_1847_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1850_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1851_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1846_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1847_recOwned;
                        isErased = false;
                        readIdents = _1849_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1167;
                        bool _out1168;
                        bool _out1169;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1170;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _1845_b), _1845_b, _564_toTpe), selfIdent, @params, mustOwn, out _out1167, out _out1168, out _out1169, out _out1170);
                        s = _out1167;
                        isOwned = _out1168;
                        isErased = _out1169;
                        readIdents = _out1170;
                      }
                    }
                  }
                } else if (_source63.is_Nullable) {
                  DAST._IType _1852___mcc_h1011 = _source63.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1853_recursiveGen;
                    bool _1854_recOwned;
                    bool _1855_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1856_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1171;
                    bool _out1172;
                    bool _out1173;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1174;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1171, out _out1172, out _out1173, out _out1174);
                    _1853_recursiveGen = _out1171;
                    _1854_recOwned = _out1172;
                    _1855_recErased = _out1173;
                    _1856_recIdents = _out1174;
                    if (!(_1854_recOwned)) {
                      _1853_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1853_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1853_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1855_recErased;
                    readIdents = _1856_recIdents;
                  }
                } else if (_source63.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1857___mcc_h1013 = _source63.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1858_recursiveGen;
                    bool _1859_recOwned;
                    bool _1860_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1861_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1175;
                    bool _out1176;
                    bool _out1177;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1178;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1175, out _out1176, out _out1177, out _out1178);
                    _1858_recursiveGen = _out1175;
                    _1859_recOwned = _out1176;
                    _1860_recErased = _out1177;
                    _1861_recIdents = _out1178;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1858_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1859_recOwned;
                    isErased = _1860_recErased;
                    readIdents = _1861_recIdents;
                  }
                } else if (_source63.is_Array) {
                  DAST._IType _1862___mcc_h1015 = _source63.dtor_element;
                  BigInteger _1863___mcc_h1016 = _source63.dtor_dims;
                  {
                    Dafny.ISequence<Dafny.Rune> _1864_recursiveGen;
                    bool _1865_recOwned;
                    bool _1866_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1867_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1179;
                    bool _out1180;
                    bool _out1181;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1182;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1179, out _out1180, out _out1181, out _out1182);
                    _1864_recursiveGen = _out1179;
                    _1865_recOwned = _out1180;
                    _1866_recErased = _out1181;
                    _1867_recIdents = _out1182;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1864_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1865_recOwned;
                    isErased = _1866_recErased;
                    readIdents = _1867_recIdents;
                  }
                } else if (_source63.is_Seq) {
                  DAST._IType _1868___mcc_h1019 = _source63.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1869_recursiveGen;
                    bool _1870_recOwned;
                    bool _1871_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1872_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1183;
                    bool _out1184;
                    bool _out1185;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1186;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1183, out _out1184, out _out1185, out _out1186);
                    _1869_recursiveGen = _out1183;
                    _1870_recOwned = _out1184;
                    _1871_recErased = _out1185;
                    _1872_recIdents = _out1186;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1869_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1870_recOwned;
                    isErased = _1871_recErased;
                    readIdents = _1872_recIdents;
                  }
                } else if (_source63.is_Set) {
                  DAST._IType _1873___mcc_h1021 = _source63.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1874_recursiveGen;
                    bool _1875_recOwned;
                    bool _1876_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1877_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1187;
                    bool _out1188;
                    bool _out1189;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1190;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1187, out _out1188, out _out1189, out _out1190);
                    _1874_recursiveGen = _out1187;
                    _1875_recOwned = _out1188;
                    _1876_recErased = _out1189;
                    _1877_recIdents = _out1190;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1874_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1875_recOwned;
                    isErased = _1876_recErased;
                    readIdents = _1877_recIdents;
                  }
                } else if (_source63.is_Multiset) {
                  DAST._IType _1878___mcc_h1023 = _source63.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1879_recursiveGen;
                    bool _1880_recOwned;
                    bool _1881_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1882_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1191;
                    bool _out1192;
                    bool _out1193;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1194;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1191, out _out1192, out _out1193, out _out1194);
                    _1879_recursiveGen = _out1191;
                    _1880_recOwned = _out1192;
                    _1881_recErased = _out1193;
                    _1882_recIdents = _out1194;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1879_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1880_recOwned;
                    isErased = _1881_recErased;
                    readIdents = _1882_recIdents;
                  }
                } else if (_source63.is_Map) {
                  DAST._IType _1883___mcc_h1025 = _source63.dtor_key;
                  DAST._IType _1884___mcc_h1026 = _source63.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1885_recursiveGen;
                    bool _1886_recOwned;
                    bool _1887_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1888_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1195;
                    bool _out1196;
                    bool _out1197;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1198;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1195, out _out1196, out _out1197, out _out1198);
                    _1885_recursiveGen = _out1195;
                    _1886_recOwned = _out1196;
                    _1887_recErased = _out1197;
                    _1888_recIdents = _out1198;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1885_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1886_recOwned;
                    isErased = _1887_recErased;
                    readIdents = _1888_recIdents;
                  }
                } else if (_source63.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1889___mcc_h1029 = _source63.dtor_args;
                  DAST._IType _1890___mcc_h1030 = _source63.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1891_recursiveGen;
                    bool _1892_recOwned;
                    bool _1893_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1894_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1199;
                    bool _out1200;
                    bool _out1201;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1202;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1199, out _out1200, out _out1201, out _out1202);
                    _1891_recursiveGen = _out1199;
                    _1892_recOwned = _out1200;
                    _1893_recErased = _out1201;
                    _1894_recIdents = _out1202;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1891_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1892_recOwned;
                    isErased = _1893_recErased;
                    readIdents = _1894_recIdents;
                  }
                } else if (_source63.is_Primitive) {
                  DAST._IPrimitive _1895___mcc_h1033 = _source63.dtor_Primitive_a0;
                  DAST._IPrimitive _source65 = _1895___mcc_h1033;
                  if (_source65.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1896_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1203;
                      _out1203 = DCOMP.COMP.GenType(_565_fromTpe, true, false);
                      _1896_rhsType = _out1203;
                      Dafny.ISequence<Dafny.Rune> _1897_recursiveGen;
                      bool _1898___v60;
                      bool _1899___v61;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1900_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1204;
                      bool _out1205;
                      bool _out1206;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1207;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, true, out _out1204, out _out1205, out _out1206, out _out1207);
                      _1897_recursiveGen = _out1204;
                      _1898___v60 = _out1205;
                      _1899___v61 = _out1206;
                      _1900_recIdents = _out1207;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from("), _1897_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as u32)"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1900_recIdents;
                    }
                  } else if (_source65.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1901_recursiveGen;
                      bool _1902_recOwned;
                      bool _1903_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1904_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1208;
                      bool _out1209;
                      bool _out1210;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1211;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1208, out _out1209, out _out1210, out _out1211);
                      _1901_recursiveGen = _out1208;
                      _1902_recOwned = _out1209;
                      _1903_recErased = _out1210;
                      _1904_recIdents = _out1211;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1901_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1902_recOwned;
                      isErased = _1903_recErased;
                      readIdents = _1904_recIdents;
                    }
                  } else if (_source65.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1905_recursiveGen;
                      bool _1906_recOwned;
                      bool _1907_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1908_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1212;
                      bool _out1213;
                      bool _out1214;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1215;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1212, out _out1213, out _out1214, out _out1215);
                      _1905_recursiveGen = _out1212;
                      _1906_recOwned = _out1213;
                      _1907_recErased = _out1214;
                      _1908_recIdents = _out1215;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1905_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1906_recOwned;
                      isErased = _1907_recErased;
                      readIdents = _1908_recIdents;
                    }
                  } else if (_source65.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1909_recursiveGen;
                      bool _1910_recOwned;
                      bool _1911_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1912_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1216;
                      bool _out1217;
                      bool _out1218;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1219;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1216, out _out1217, out _out1218, out _out1219);
                      _1909_recursiveGen = _out1216;
                      _1910_recOwned = _out1217;
                      _1911_recErased = _out1218;
                      _1912_recIdents = _out1219;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1909_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1910_recOwned;
                      isErased = _1911_recErased;
                      readIdents = _1912_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1913_recursiveGen;
                      bool _1914_recOwned;
                      bool _1915_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1916_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1220;
                      bool _out1221;
                      bool _out1222;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1223;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1220, out _out1221, out _out1222, out _out1223);
                      _1913_recursiveGen = _out1220;
                      _1914_recOwned = _out1221;
                      _1915_recErased = _out1222;
                      _1916_recIdents = _out1223;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1913_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1914_recOwned;
                      isErased = _1915_recErased;
                      readIdents = _1916_recIdents;
                    }
                  }
                } else if (_source63.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1917___mcc_h1035 = _source63.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1918_recursiveGen;
                    bool _1919_recOwned;
                    bool _1920_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1921_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1224;
                    bool _out1225;
                    bool _out1226;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1227;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1224, out _out1225, out _out1226, out _out1227);
                    _1918_recursiveGen = _out1224;
                    _1919_recOwned = _out1225;
                    _1920_recErased = _out1226;
                    _1921_recIdents = _out1227;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1918_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1919_recOwned;
                    isErased = _1920_recErased;
                    readIdents = _1921_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1922___mcc_h1037 = _source63.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1923_recursiveGen;
                    bool _1924_recOwned;
                    bool _1925_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1926_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1228;
                    bool _out1229;
                    bool _out1230;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1231;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1228, out _out1229, out _out1230, out _out1231);
                    _1923_recursiveGen = _out1228;
                    _1924_recOwned = _out1229;
                    _1925_recErased = _out1230;
                    _1926_recIdents = _out1231;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1923_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1924_recOwned;
                    isErased = _1925_recErased;
                    readIdents = _1926_recIdents;
                  }
                }
              }
            } else if (_source28.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1927___mcc_h1039 = _source28.dtor_Passthrough_a0;
              DAST._IType _source66 = _572___mcc_h284;
              if (_source66.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1928___mcc_h1043 = _source66.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1929___mcc_h1044 = _source66.dtor_typeArgs;
                DAST._IResolvedType _1930___mcc_h1045 = _source66.dtor_resolved;
                DAST._IResolvedType _source67 = _1930___mcc_h1045;
                if (_source67.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1931___mcc_h1049 = _source67.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1932_recursiveGen;
                    bool _1933_recOwned;
                    bool _1934_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1935_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1232;
                    bool _out1233;
                    bool _out1234;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1235;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1232, out _out1233, out _out1234, out _out1235);
                    _1932_recursiveGen = _out1232;
                    _1933_recOwned = _out1233;
                    _1934_recErased = _out1234;
                    _1935_recIdents = _out1235;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1932_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1933_recOwned;
                    isErased = _1934_recErased;
                    readIdents = _1935_recIdents;
                  }
                } else if (_source67.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1936___mcc_h1051 = _source67.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1937_recursiveGen;
                    bool _1938_recOwned;
                    bool _1939_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1940_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1236;
                    bool _out1237;
                    bool _out1238;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1239;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1236, out _out1237, out _out1238, out _out1239);
                    _1937_recursiveGen = _out1236;
                    _1938_recOwned = _out1237;
                    _1939_recErased = _out1238;
                    _1940_recIdents = _out1239;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1937_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1938_recOwned;
                    isErased = _1939_recErased;
                    readIdents = _1940_recIdents;
                  }
                } else {
                  DAST._IType _1941___mcc_h1053 = _source67.dtor_Newtype_a0;
                  DAST._IType _1942_b = _1941___mcc_h1053;
                  {
                    if (object.Equals(_565_fromTpe, _1942_b)) {
                      Dafny.ISequence<Dafny.Rune> _1943_recursiveGen;
                      bool _1944_recOwned;
                      bool _1945_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1946_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1240;
                      bool _out1241;
                      bool _out1242;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1243;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1240, out _out1241, out _out1242, out _out1243);
                      _1943_recursiveGen = _out1240;
                      _1944_recOwned = _out1241;
                      _1945_recErased = _out1242;
                      _1946_recIdents = _out1243;
                      Dafny.ISequence<Dafny.Rune> _1947_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1244;
                      _out1244 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                      _1947_rhsType = _out1244;
                      Dafny.ISequence<Dafny.Rune> _1948_uneraseFn;
                      _1948_uneraseFn = ((_1944_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1947_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1948_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1943_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1944_recOwned;
                      isErased = false;
                      readIdents = _1946_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out1245;
                      bool _out1246;
                      bool _out1247;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1248;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _1942_b), _1942_b, _564_toTpe), selfIdent, @params, mustOwn, out _out1245, out _out1246, out _out1247, out _out1248);
                      s = _out1245;
                      isOwned = _out1246;
                      isErased = _out1247;
                      readIdents = _out1248;
                    }
                  }
                }
              } else if (_source66.is_Nullable) {
                DAST._IType _1949___mcc_h1055 = _source66.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1950_recursiveGen;
                  bool _1951_recOwned;
                  bool _1952_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1953_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1249;
                  bool _out1250;
                  bool _out1251;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1252;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1249, out _out1250, out _out1251, out _out1252);
                  _1950_recursiveGen = _out1249;
                  _1951_recOwned = _out1250;
                  _1952_recErased = _out1251;
                  _1953_recIdents = _out1252;
                  if (!(_1951_recOwned)) {
                    _1950_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1950_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1950_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1952_recErased;
                  readIdents = _1953_recIdents;
                }
              } else if (_source66.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1954___mcc_h1057 = _source66.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1955_recursiveGen;
                  bool _1956_recOwned;
                  bool _1957_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1958_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1253;
                  bool _out1254;
                  bool _out1255;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1256;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1253, out _out1254, out _out1255, out _out1256);
                  _1955_recursiveGen = _out1253;
                  _1956_recOwned = _out1254;
                  _1957_recErased = _out1255;
                  _1958_recIdents = _out1256;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1955_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1956_recOwned;
                  isErased = _1957_recErased;
                  readIdents = _1958_recIdents;
                }
              } else if (_source66.is_Array) {
                DAST._IType _1959___mcc_h1059 = _source66.dtor_element;
                BigInteger _1960___mcc_h1060 = _source66.dtor_dims;
                {
                  Dafny.ISequence<Dafny.Rune> _1961_recursiveGen;
                  bool _1962_recOwned;
                  bool _1963_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1964_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1257;
                  bool _out1258;
                  bool _out1259;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1260;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1257, out _out1258, out _out1259, out _out1260);
                  _1961_recursiveGen = _out1257;
                  _1962_recOwned = _out1258;
                  _1963_recErased = _out1259;
                  _1964_recIdents = _out1260;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1961_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1962_recOwned;
                  isErased = _1963_recErased;
                  readIdents = _1964_recIdents;
                }
              } else if (_source66.is_Seq) {
                DAST._IType _1965___mcc_h1063 = _source66.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1966_recursiveGen;
                  bool _1967_recOwned;
                  bool _1968_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1969_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1261;
                  bool _out1262;
                  bool _out1263;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1264;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1261, out _out1262, out _out1263, out _out1264);
                  _1966_recursiveGen = _out1261;
                  _1967_recOwned = _out1262;
                  _1968_recErased = _out1263;
                  _1969_recIdents = _out1264;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1966_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1967_recOwned;
                  isErased = _1968_recErased;
                  readIdents = _1969_recIdents;
                }
              } else if (_source66.is_Set) {
                DAST._IType _1970___mcc_h1065 = _source66.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1971_recursiveGen;
                  bool _1972_recOwned;
                  bool _1973_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1974_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1265;
                  bool _out1266;
                  bool _out1267;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1268;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1265, out _out1266, out _out1267, out _out1268);
                  _1971_recursiveGen = _out1265;
                  _1972_recOwned = _out1266;
                  _1973_recErased = _out1267;
                  _1974_recIdents = _out1268;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1971_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1972_recOwned;
                  isErased = _1973_recErased;
                  readIdents = _1974_recIdents;
                }
              } else if (_source66.is_Multiset) {
                DAST._IType _1975___mcc_h1067 = _source66.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1976_recursiveGen;
                  bool _1977_recOwned;
                  bool _1978_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1979_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1269;
                  bool _out1270;
                  bool _out1271;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1272;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1269, out _out1270, out _out1271, out _out1272);
                  _1976_recursiveGen = _out1269;
                  _1977_recOwned = _out1270;
                  _1978_recErased = _out1271;
                  _1979_recIdents = _out1272;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1976_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1977_recOwned;
                  isErased = _1978_recErased;
                  readIdents = _1979_recIdents;
                }
              } else if (_source66.is_Map) {
                DAST._IType _1980___mcc_h1069 = _source66.dtor_key;
                DAST._IType _1981___mcc_h1070 = _source66.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1982_recursiveGen;
                  bool _1983_recOwned;
                  bool _1984_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1985_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1273;
                  bool _out1274;
                  bool _out1275;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1276;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1273, out _out1274, out _out1275, out _out1276);
                  _1982_recursiveGen = _out1273;
                  _1983_recOwned = _out1274;
                  _1984_recErased = _out1275;
                  _1985_recIdents = _out1276;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1982_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1983_recOwned;
                  isErased = _1984_recErased;
                  readIdents = _1985_recIdents;
                }
              } else if (_source66.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1986___mcc_h1073 = _source66.dtor_args;
                DAST._IType _1987___mcc_h1074 = _source66.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1988_recursiveGen;
                  bool _1989_recOwned;
                  bool _1990_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1991_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1277;
                  bool _out1278;
                  bool _out1279;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1280;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1277, out _out1278, out _out1279, out _out1280);
                  _1988_recursiveGen = _out1277;
                  _1989_recOwned = _out1278;
                  _1990_recErased = _out1279;
                  _1991_recIdents = _out1280;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1988_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1989_recOwned;
                  isErased = _1990_recErased;
                  readIdents = _1991_recIdents;
                }
              } else if (_source66.is_Primitive) {
                DAST._IPrimitive _1992___mcc_h1077 = _source66.dtor_Primitive_a0;
                DAST._IPrimitive _source68 = _1992___mcc_h1077;
                if (_source68.is_Int) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1993_rhsType;
                    Dafny.ISequence<Dafny.Rune> _out1281;
                    _out1281 = DCOMP.COMP.GenType(_565_fromTpe, true, false);
                    _1993_rhsType = _out1281;
                    Dafny.ISequence<Dafny.Rune> _1994_recursiveGen;
                    bool _1995___v56;
                    bool _1996___v57;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1997_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1282;
                    bool _out1283;
                    bool _out1284;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1285;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, true, out _out1282, out _out1283, out _out1284, out _out1285);
                    _1994_recursiveGen = _out1282;
                    _1995___v56 = _out1283;
                    _1996___v57 = _out1284;
                    _1997_recIdents = _out1285;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from("), _1994_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = true;
                    readIdents = _1997_recIdents;
                  }
                } else if (_source68.is_Real) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1998_recursiveGen;
                    bool _1999_recOwned;
                    bool _2000_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2001_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1286;
                    bool _out1287;
                    bool _out1288;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1289;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1286, out _out1287, out _out1288, out _out1289);
                    _1998_recursiveGen = _out1286;
                    _1999_recOwned = _out1287;
                    _2000_recErased = _out1288;
                    _2001_recIdents = _out1289;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1998_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1999_recOwned;
                    isErased = _2000_recErased;
                    readIdents = _2001_recIdents;
                  }
                } else if (_source68.is_String) {
                  {
                    Dafny.ISequence<Dafny.Rune> _2002_recursiveGen;
                    bool _2003_recOwned;
                    bool _2004_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2005_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1290;
                    bool _out1291;
                    bool _out1292;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1293;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1290, out _out1291, out _out1292, out _out1293);
                    _2002_recursiveGen = _out1290;
                    _2003_recOwned = _out1291;
                    _2004_recErased = _out1292;
                    _2005_recIdents = _out1293;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2002_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _2003_recOwned;
                    isErased = _2004_recErased;
                    readIdents = _2005_recIdents;
                  }
                } else if (_source68.is_Bool) {
                  {
                    Dafny.ISequence<Dafny.Rune> _2006_recursiveGen;
                    bool _2007_recOwned;
                    bool _2008_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2009_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1294;
                    bool _out1295;
                    bool _out1296;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1297;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1294, out _out1295, out _out1296, out _out1297);
                    _2006_recursiveGen = _out1294;
                    _2007_recOwned = _out1295;
                    _2008_recErased = _out1296;
                    _2009_recIdents = _out1297;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2006_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _2007_recOwned;
                    isErased = _2008_recErased;
                    readIdents = _2009_recIdents;
                  }
                } else {
                  {
                    Dafny.ISequence<Dafny.Rune> _2010_recursiveGen;
                    bool _2011_recOwned;
                    bool _2012_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2013_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1298;
                    bool _out1299;
                    bool _out1300;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1301;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1298, out _out1299, out _out1300, out _out1301);
                    _2010_recursiveGen = _out1298;
                    _2011_recOwned = _out1299;
                    _2012_recErased = _out1300;
                    _2013_recIdents = _out1301;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2010_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _2011_recOwned;
                    isErased = _2012_recErased;
                    readIdents = _2013_recIdents;
                  }
                }
              } else if (_source66.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _2014___mcc_h1079 = _source66.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2015_recursiveGen;
                  bool _2016___v64;
                  bool _2017___v65;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2018_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1302;
                  bool _out1303;
                  bool _out1304;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1305;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, true, out _out1302, out _out1303, out _out1304, out _out1305);
                  _2015_recursiveGen = _out1302;
                  _2016___v64 = _out1303;
                  _2017___v65 = _out1304;
                  _2018_recIdents = _out1305;
                  Dafny.ISequence<Dafny.Rune> _2019_toTpeGen;
                  Dafny.ISequence<Dafny.Rune> _out1306;
                  _out1306 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                  _2019_toTpeGen = _out1306;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), _2015_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), _2019_toTpeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = true;
                  readIdents = _2018_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _2020___mcc_h1081 = _source66.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2021_recursiveGen;
                  bool _2022_recOwned;
                  bool _2023_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2024_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1307;
                  bool _out1308;
                  bool _out1309;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1310;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1307, out _out1308, out _out1309, out _out1310);
                  _2021_recursiveGen = _out1307;
                  _2022_recOwned = _out1308;
                  _2023_recErased = _out1309;
                  _2024_recIdents = _out1310;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2021_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2022_recOwned;
                  isErased = _2023_recErased;
                  readIdents = _2024_recIdents;
                }
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2025___mcc_h1083 = _source28.dtor_TypeArg_a0;
              DAST._IType _source69 = _572___mcc_h284;
              if (_source69.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2026___mcc_h1087 = _source69.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _2027___mcc_h1088 = _source69.dtor_typeArgs;
                DAST._IResolvedType _2028___mcc_h1089 = _source69.dtor_resolved;
                DAST._IResolvedType _source70 = _2028___mcc_h1089;
                if (_source70.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2029___mcc_h1093 = _source70.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _2030_recursiveGen;
                    bool _2031_recOwned;
                    bool _2032_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2033_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1311;
                    bool _out1312;
                    bool _out1313;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1314;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1311, out _out1312, out _out1313, out _out1314);
                    _2030_recursiveGen = _out1311;
                    _2031_recOwned = _out1312;
                    _2032_recErased = _out1313;
                    _2033_recIdents = _out1314;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2030_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _2031_recOwned;
                    isErased = _2032_recErased;
                    readIdents = _2033_recIdents;
                  }
                } else if (_source70.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2034___mcc_h1095 = _source70.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _2035_recursiveGen;
                    bool _2036_recOwned;
                    bool _2037_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2038_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1315;
                    bool _out1316;
                    bool _out1317;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1318;
                    DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1315, out _out1316, out _out1317, out _out1318);
                    _2035_recursiveGen = _out1315;
                    _2036_recOwned = _out1316;
                    _2037_recErased = _out1317;
                    _2038_recIdents = _out1318;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2035_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _2036_recOwned;
                    isErased = _2037_recErased;
                    readIdents = _2038_recIdents;
                  }
                } else {
                  DAST._IType _2039___mcc_h1097 = _source70.dtor_Newtype_a0;
                  DAST._IType _2040_b = _2039___mcc_h1097;
                  {
                    if (object.Equals(_565_fromTpe, _2040_b)) {
                      Dafny.ISequence<Dafny.Rune> _2041_recursiveGen;
                      bool _2042_recOwned;
                      bool _2043_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2044_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1319;
                      bool _out1320;
                      bool _out1321;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1322;
                      DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1319, out _out1320, out _out1321, out _out1322);
                      _2041_recursiveGen = _out1319;
                      _2042_recOwned = _out1320;
                      _2043_recErased = _out1321;
                      _2044_recIdents = _out1322;
                      Dafny.ISequence<Dafny.Rune> _2045_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1323;
                      _out1323 = DCOMP.COMP.GenType(_564_toTpe, true, false);
                      _2045_rhsType = _out1323;
                      Dafny.ISequence<Dafny.Rune> _2046_uneraseFn;
                      _2046_uneraseFn = ((_2042_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2045_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _2046_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2041_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _2042_recOwned;
                      isErased = false;
                      readIdents = _2044_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out1324;
                      bool _out1325;
                      bool _out1326;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1327;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_566_expr, _565_fromTpe, _2040_b), _2040_b, _564_toTpe), selfIdent, @params, mustOwn, out _out1324, out _out1325, out _out1326, out _out1327);
                      s = _out1324;
                      isOwned = _out1325;
                      isErased = _out1326;
                      readIdents = _out1327;
                    }
                  }
                }
              } else if (_source69.is_Nullable) {
                DAST._IType _2047___mcc_h1099 = _source69.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2048_recursiveGen;
                  bool _2049_recOwned;
                  bool _2050_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2051_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1328;
                  bool _out1329;
                  bool _out1330;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1331;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1328, out _out1329, out _out1330, out _out1331);
                  _2048_recursiveGen = _out1328;
                  _2049_recOwned = _out1329;
                  _2050_recErased = _out1330;
                  _2051_recIdents = _out1331;
                  if (!(_2049_recOwned)) {
                    _2048_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_2048_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _2048_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _2050_recErased;
                  readIdents = _2051_recIdents;
                }
              } else if (_source69.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2052___mcc_h1101 = _source69.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2053_recursiveGen;
                  bool _2054_recOwned;
                  bool _2055_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2056_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1332;
                  bool _out1333;
                  bool _out1334;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1335;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1332, out _out1333, out _out1334, out _out1335);
                  _2053_recursiveGen = _out1332;
                  _2054_recOwned = _out1333;
                  _2055_recErased = _out1334;
                  _2056_recIdents = _out1335;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2053_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2054_recOwned;
                  isErased = _2055_recErased;
                  readIdents = _2056_recIdents;
                }
              } else if (_source69.is_Array) {
                DAST._IType _2057___mcc_h1103 = _source69.dtor_element;
                BigInteger _2058___mcc_h1104 = _source69.dtor_dims;
                {
                  Dafny.ISequence<Dafny.Rune> _2059_recursiveGen;
                  bool _2060_recOwned;
                  bool _2061_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2062_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1336;
                  bool _out1337;
                  bool _out1338;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1339;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1336, out _out1337, out _out1338, out _out1339);
                  _2059_recursiveGen = _out1336;
                  _2060_recOwned = _out1337;
                  _2061_recErased = _out1338;
                  _2062_recIdents = _out1339;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2059_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2060_recOwned;
                  isErased = _2061_recErased;
                  readIdents = _2062_recIdents;
                }
              } else if (_source69.is_Seq) {
                DAST._IType _2063___mcc_h1107 = _source69.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _2064_recursiveGen;
                  bool _2065_recOwned;
                  bool _2066_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2067_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1340;
                  bool _out1341;
                  bool _out1342;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1343;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1340, out _out1341, out _out1342, out _out1343);
                  _2064_recursiveGen = _out1340;
                  _2065_recOwned = _out1341;
                  _2066_recErased = _out1342;
                  _2067_recIdents = _out1343;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2064_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2065_recOwned;
                  isErased = _2066_recErased;
                  readIdents = _2067_recIdents;
                }
              } else if (_source69.is_Set) {
                DAST._IType _2068___mcc_h1109 = _source69.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _2069_recursiveGen;
                  bool _2070_recOwned;
                  bool _2071_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2072_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1344;
                  bool _out1345;
                  bool _out1346;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1347;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1344, out _out1345, out _out1346, out _out1347);
                  _2069_recursiveGen = _out1344;
                  _2070_recOwned = _out1345;
                  _2071_recErased = _out1346;
                  _2072_recIdents = _out1347;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2069_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2070_recOwned;
                  isErased = _2071_recErased;
                  readIdents = _2072_recIdents;
                }
              } else if (_source69.is_Multiset) {
                DAST._IType _2073___mcc_h1111 = _source69.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _2074_recursiveGen;
                  bool _2075_recOwned;
                  bool _2076_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2077_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1348;
                  bool _out1349;
                  bool _out1350;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1351;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1348, out _out1349, out _out1350, out _out1351);
                  _2074_recursiveGen = _out1348;
                  _2075_recOwned = _out1349;
                  _2076_recErased = _out1350;
                  _2077_recIdents = _out1351;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2074_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2075_recOwned;
                  isErased = _2076_recErased;
                  readIdents = _2077_recIdents;
                }
              } else if (_source69.is_Map) {
                DAST._IType _2078___mcc_h1113 = _source69.dtor_key;
                DAST._IType _2079___mcc_h1114 = _source69.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _2080_recursiveGen;
                  bool _2081_recOwned;
                  bool _2082_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2083_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1352;
                  bool _out1353;
                  bool _out1354;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1355;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1352, out _out1353, out _out1354, out _out1355);
                  _2080_recursiveGen = _out1352;
                  _2081_recOwned = _out1353;
                  _2082_recErased = _out1354;
                  _2083_recIdents = _out1355;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2080_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2081_recOwned;
                  isErased = _2082_recErased;
                  readIdents = _2083_recIdents;
                }
              } else if (_source69.is_Arrow) {
                Dafny.ISequence<DAST._IType> _2084___mcc_h1117 = _source69.dtor_args;
                DAST._IType _2085___mcc_h1118 = _source69.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _2086_recursiveGen;
                  bool _2087_recOwned;
                  bool _2088_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2089_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1356;
                  bool _out1357;
                  bool _out1358;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1359;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1356, out _out1357, out _out1358, out _out1359);
                  _2086_recursiveGen = _out1356;
                  _2087_recOwned = _out1357;
                  _2088_recErased = _out1358;
                  _2089_recIdents = _out1359;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2086_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2087_recOwned;
                  isErased = _2088_recErased;
                  readIdents = _2089_recIdents;
                }
              } else if (_source69.is_Primitive) {
                DAST._IPrimitive _2090___mcc_h1121 = _source69.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2091_recursiveGen;
                  bool _2092_recOwned;
                  bool _2093_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2094_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1360;
                  bool _out1361;
                  bool _out1362;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1363;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1360, out _out1361, out _out1362, out _out1363);
                  _2091_recursiveGen = _out1360;
                  _2092_recOwned = _out1361;
                  _2093_recErased = _out1362;
                  _2094_recIdents = _out1363;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2091_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2092_recOwned;
                  isErased = _2093_recErased;
                  readIdents = _2094_recIdents;
                }
              } else if (_source69.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _2095___mcc_h1123 = _source69.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2096_recursiveGen;
                  bool _2097_recOwned;
                  bool _2098_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2099_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1364;
                  bool _out1365;
                  bool _out1366;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1367;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1364, out _out1365, out _out1366, out _out1367);
                  _2096_recursiveGen = _out1364;
                  _2097_recOwned = _out1365;
                  _2098_recErased = _out1366;
                  _2099_recIdents = _out1367;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2096_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2097_recOwned;
                  isErased = _2098_recErased;
                  readIdents = _2099_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _2100___mcc_h1125 = _source69.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2101_recursiveGen;
                  bool _2102_recOwned;
                  bool _2103_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2104_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1368;
                  bool _out1369;
                  bool _out1370;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1371;
                  DCOMP.COMP.GenExpr(_566_expr, selfIdent, @params, mustOwn, out _out1368, out _out1369, out _out1370, out _out1371);
                  _2101_recursiveGen = _out1368;
                  _2102_recOwned = _out1369;
                  _2103_recErased = _out1370;
                  _2104_recIdents = _out1371;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2101_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2102_recOwned;
                  isErased = _2103_recErased;
                  readIdents = _2104_recIdents;
                }
              }
            }
          }
        }
      } else if (_source21.is_SeqConstruct) {
        DAST._IExpression _2105___mcc_h22 = _source21.dtor_length;
        DAST._IExpression _2106___mcc_h23 = _source21.dtor_elem;
        DAST._IExpression _2107_expr = _2106___mcc_h23;
        DAST._IExpression _2108_length = _2105___mcc_h22;
        {
          Dafny.ISequence<Dafny.Rune> _2109_recursiveGen;
          bool _2110___v67;
          bool _2111_eErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2112_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1372;
          bool _out1373;
          bool _out1374;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1375;
          DCOMP.COMP.GenExpr(_2107_expr, selfIdent, @params, true, out _out1372, out _out1373, out _out1374, out _out1375);
          _2109_recursiveGen = _out1372;
          _2110___v67 = _out1373;
          _2111_eErased = _out1374;
          _2112_recIdents = _out1375;
          Dafny.ISequence<Dafny.Rune> _2113_lengthGen;
          bool _2114___v68;
          bool _2115_lengthErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2116_lengthIdents;
          Dafny.ISequence<Dafny.Rune> _out1376;
          bool _out1377;
          bool _out1378;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1379;
          DCOMP.COMP.GenExpr(_2108_length, selfIdent, @params, true, out _out1376, out _out1377, out _out1378, out _out1379);
          _2113_lengthGen = _out1376;
          _2114___v68 = _out1377;
          _2115_lengthErased = _out1378;
          _2116_lengthIdents = _out1379;
          if (!(_2115_lengthErased)) {
            _2113_lengthGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2113_lengthGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), _2109_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), _2113_lengthGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer.0(&i)).collect::<Vec<_>>()\n}"));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2112_recIdents, _2116_lengthIdents);
          isOwned = true;
          isErased = _2111_eErased;
        }
      } else if (_source21.is_SeqValue) {
        Dafny.ISequence<DAST._IExpression> _2117___mcc_h24 = _source21.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _2118_exprs = _2117___mcc_h24;
        {
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>> _2119_generatedValues;
          _2119_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2120_i;
          _2120_i = BigInteger.Zero;
          bool _2121_allErased;
          _2121_allErased = true;
          while ((_2120_i) < (new BigInteger((_2118_exprs).Count))) {
            Dafny.ISequence<Dafny.Rune> _2122_recursiveGen;
            bool _2123___v69;
            bool _2124_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2125_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1380;
            bool _out1381;
            bool _out1382;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1383;
            DCOMP.COMP.GenExpr((_2118_exprs).Select(_2120_i), selfIdent, @params, true, out _out1380, out _out1381, out _out1382, out _out1383);
            _2122_recursiveGen = _out1380;
            _2123___v69 = _out1381;
            _2124_isErased = _out1382;
            _2125_recIdents = _out1383;
            _2121_allErased = (_2121_allErased) && (_2124_isErased);
            _2119_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.Concat(_2119_generatedValues, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, bool>.create(_2122_recursiveGen, _2124_isErased)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2125_recIdents);
            _2120_i = (_2120_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec![");
          _2120_i = BigInteger.Zero;
          while ((_2120_i) < (new BigInteger((_2119_generatedValues).Count))) {
            if ((_2120_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2126_gen;
            _2126_gen = ((_2119_generatedValues).Select(_2120_i)).dtor__0;
            if ((((_2119_generatedValues).Select(_2120_i)).dtor__1) && (!(_2121_allErased))) {
              _2126_gen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _2126_gen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2126_gen);
            _2120_i = (_2120_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
          isOwned = true;
          isErased = _2121_allErased;
        }
      } else if (_source21.is_SetValue) {
        Dafny.ISequence<DAST._IExpression> _2127___mcc_h25 = _source21.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _2128_exprs = _2127___mcc_h25;
        {
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>> _2129_generatedValues;
          _2129_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2130_i;
          _2130_i = BigInteger.Zero;
          bool _2131_allErased;
          _2131_allErased = true;
          while ((_2130_i) < (new BigInteger((_2128_exprs).Count))) {
            Dafny.ISequence<Dafny.Rune> _2132_recursiveGen;
            bool _2133___v70;
            bool _2134_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2135_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1384;
            bool _out1385;
            bool _out1386;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1387;
            DCOMP.COMP.GenExpr((_2128_exprs).Select(_2130_i), selfIdent, @params, true, out _out1384, out _out1385, out _out1386, out _out1387);
            _2132_recursiveGen = _out1384;
            _2133___v70 = _out1385;
            _2134_isErased = _out1386;
            _2135_recIdents = _out1387;
            _2131_allErased = (_2131_allErased) && (_2134_isErased);
            _2129_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.Concat(_2129_generatedValues, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, bool>.create(_2132_recursiveGen, _2134_isErased)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2135_recIdents);
            _2130_i = (_2130_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec![");
          _2130_i = BigInteger.Zero;
          while ((_2130_i) < (new BigInteger((_2129_generatedValues).Count))) {
            if ((_2130_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2136_gen;
            _2136_gen = ((_2129_generatedValues).Select(_2130_i)).dtor__0;
            if ((((_2129_generatedValues).Select(_2130_i)).dtor__1) && (!(_2131_allErased))) {
              _2136_gen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _2136_gen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2136_gen);
            _2130_i = (_2130_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("].into_iter().collect::<std::collections::HashSet<_>>()"));
          isOwned = true;
          isErased = _2131_allErased;
        }
      } else if (_source21.is_MapValue) {
        Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2137___mcc_h26 = _source21.dtor_mapElems;
        Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2138_mapElems = _2137___mcc_h26;
        {
          Dafny.ISequence<_System._ITuple4<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>, bool, bool>> _2139_generatedValues;
          _2139_generatedValues = Dafny.Sequence<_System._ITuple4<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>, bool, bool>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2140_i;
          _2140_i = BigInteger.Zero;
          bool _2141_allErased;
          _2141_allErased = true;
          while ((_2140_i) < (new BigInteger((_2138_mapElems).Count))) {
            Dafny.ISequence<Dafny.Rune> _2142_recursiveGenKey;
            bool _2143___v71;
            bool _2144_isErasedKey;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2145_recIdentsKey;
            Dafny.ISequence<Dafny.Rune> _out1388;
            bool _out1389;
            bool _out1390;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1391;
            DCOMP.COMP.GenExpr(((_2138_mapElems).Select(_2140_i)).dtor__0, selfIdent, @params, true, out _out1388, out _out1389, out _out1390, out _out1391);
            _2142_recursiveGenKey = _out1388;
            _2143___v71 = _out1389;
            _2144_isErasedKey = _out1390;
            _2145_recIdentsKey = _out1391;
            Dafny.ISequence<Dafny.Rune> _2146_recursiveGenValue;
            bool _2147___v72;
            bool _2148_isErasedValue;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2149_recIdentsValue;
            Dafny.ISequence<Dafny.Rune> _out1392;
            bool _out1393;
            bool _out1394;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1395;
            DCOMP.COMP.GenExpr(((_2138_mapElems).Select(_2140_i)).dtor__1, selfIdent, @params, true, out _out1392, out _out1393, out _out1394, out _out1395);
            _2146_recursiveGenValue = _out1392;
            _2147___v72 = _out1393;
            _2148_isErasedValue = _out1394;
            _2149_recIdentsValue = _out1395;
            _2141_allErased = ((_2141_allErased) && (_2144_isErasedKey)) && (_2148_isErasedValue);
            _2139_generatedValues = Dafny.Sequence<_System._ITuple4<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>, bool, bool>>.Concat(_2139_generatedValues, Dafny.Sequence<_System._ITuple4<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>, bool, bool>>.FromElements(_System.Tuple4<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>, bool, bool>.create(_2142_recursiveGenKey, _2146_recursiveGenValue, _2144_isErasedKey, _2148_isErasedValue)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2145_recIdentsKey), _2149_recIdentsValue);
            _2140_i = (_2140_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec![");
          _2140_i = BigInteger.Zero;
          while ((_2140_i) < (new BigInteger((_2139_generatedValues).Count))) {
            if ((_2140_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2150_genKey;
            _2150_genKey = ((_2139_generatedValues).Select(_2140_i)).dtor__0;
            Dafny.ISequence<Dafny.Rune> _2151_genValue;
            _2151_genValue = ((_2139_generatedValues).Select(_2140_i)).dtor__1;
            if ((((_2139_generatedValues).Select(_2140_i)).dtor__2) && (!(_2141_allErased))) {
              _2150_genKey = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _2150_genKey), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((((_2139_generatedValues).Select(_2140_i)).dtor__3) && (!(_2141_allErased))) {
              _2151_genValue = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _2151_genValue), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2150_genKey), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _2151_genValue), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            _2140_i = (_2140_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("].into_iter().collect::<std::collections::HashMap<_, _>>()"));
          isOwned = true;
          isErased = _2141_allErased;
        }
      } else if (_source21.is_This) {
        {
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _source71 = selfIdent;
          if (_source71.is_Some) {
            Dafny.ISequence<Dafny.Rune> _2152___mcc_h1127 = _source71.dtor_Some_a0;
            Dafny.ISequence<Dafny.Rune> _2153_id = _2152___mcc_h1127;
            {
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(_2153_id, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                isOwned = true;
              } else {
                if ((_2153_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
                } else {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2153_id);
                }
                isOwned = false;
              }
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2153_id);
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
        DAST._IExpression _2154___mcc_h27 = _source21.dtor_cond;
        DAST._IExpression _2155___mcc_h28 = _source21.dtor_thn;
        DAST._IExpression _2156___mcc_h29 = _source21.dtor_els;
        DAST._IExpression _2157_f = _2156___mcc_h29;
        DAST._IExpression _2158_t = _2155___mcc_h28;
        DAST._IExpression _2159_cond = _2154___mcc_h27;
        {
          Dafny.ISequence<Dafny.Rune> _2160_condString;
          bool _2161___v73;
          bool _2162_condErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2163_recIdentsCond;
          Dafny.ISequence<Dafny.Rune> _out1396;
          bool _out1397;
          bool _out1398;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1399;
          DCOMP.COMP.GenExpr(_2159_cond, selfIdent, @params, true, out _out1396, out _out1397, out _out1398, out _out1399);
          _2160_condString = _out1396;
          _2161___v73 = _out1397;
          _2162_condErased = _out1398;
          _2163_recIdentsCond = _out1399;
          if (!(_2162_condErased)) {
            _2160_condString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2160_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          Dafny.ISequence<Dafny.Rune> _2164___v74;
          bool _2165_tHasToBeOwned;
          bool _2166___v75;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2167___v76;
          Dafny.ISequence<Dafny.Rune> _out1400;
          bool _out1401;
          bool _out1402;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1403;
          DCOMP.COMP.GenExpr(_2158_t, selfIdent, @params, mustOwn, out _out1400, out _out1401, out _out1402, out _out1403);
          _2164___v74 = _out1400;
          _2165_tHasToBeOwned = _out1401;
          _2166___v75 = _out1402;
          _2167___v76 = _out1403;
          Dafny.ISequence<Dafny.Rune> _2168_fString;
          bool _2169_fOwned;
          bool _2170_fErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2171_recIdentsF;
          Dafny.ISequence<Dafny.Rune> _out1404;
          bool _out1405;
          bool _out1406;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1407;
          DCOMP.COMP.GenExpr(_2157_f, selfIdent, @params, _2165_tHasToBeOwned, out _out1404, out _out1405, out _out1406, out _out1407);
          _2168_fString = _out1404;
          _2169_fOwned = _out1405;
          _2170_fErased = _out1406;
          _2171_recIdentsF = _out1407;
          Dafny.ISequence<Dafny.Rune> _2172_tString;
          bool _2173___v77;
          bool _2174_tErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2175_recIdentsT;
          Dafny.ISequence<Dafny.Rune> _out1408;
          bool _out1409;
          bool _out1410;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1411;
          DCOMP.COMP.GenExpr(_2158_t, selfIdent, @params, _2169_fOwned, out _out1408, out _out1409, out _out1410, out _out1411);
          _2172_tString = _out1408;
          _2173___v77 = _out1409;
          _2174_tErased = _out1410;
          _2175_recIdentsT = _out1411;
          if ((!(_2170_fErased)) || (!(_2174_tErased))) {
            if (_2170_fErased) {
              _2168_fString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2168_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if (_2174_tErased) {
              _2172_tString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2172_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _2160_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _2172_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _2168_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})"));
          isOwned = _2169_fOwned;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2163_recIdentsCond, _2175_recIdentsT), _2171_recIdentsF);
          isErased = (_2170_fErased) || (_2174_tErased);
        }
      } else if (_source21.is_UnOp) {
        DAST._IUnaryOp _2176___mcc_h30 = _source21.dtor_unOp;
        DAST._IExpression _2177___mcc_h31 = _source21.dtor_expr;
        DAST._IUnaryOp _source72 = _2176___mcc_h30;
        if (_source72.is_Not) {
          DAST._IExpression _2178_e = _2177___mcc_h31;
          {
            Dafny.ISequence<Dafny.Rune> _2179_recursiveGen;
            bool _2180___v78;
            bool _2181_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2182_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1412;
            bool _out1413;
            bool _out1414;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1415;
            DCOMP.COMP.GenExpr(_2178_e, selfIdent, @params, true, out _out1412, out _out1413, out _out1414, out _out1415);
            _2179_recursiveGen = _out1412;
            _2180___v78 = _out1413;
            _2181_recErased = _out1414;
            _2182_recIdents = _out1415;
            if (!(_2181_recErased)) {
              _2179_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2179_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!("), _2179_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _2182_recIdents;
            isErased = true;
          }
        } else if (_source72.is_BitwiseNot) {
          DAST._IExpression _2183_e = _2177___mcc_h31;
          {
            Dafny.ISequence<Dafny.Rune> _2184_recursiveGen;
            bool _2185___v79;
            bool _2186_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2187_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1416;
            bool _out1417;
            bool _out1418;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1419;
            DCOMP.COMP.GenExpr(_2183_e, selfIdent, @params, true, out _out1416, out _out1417, out _out1418, out _out1419);
            _2184_recursiveGen = _out1416;
            _2185___v79 = _out1417;
            _2186_recErased = _out1418;
            _2187_recIdents = _out1419;
            if (!(_2186_recErased)) {
              _2184_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2184_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~("), _2184_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _2187_recIdents;
            isErased = true;
          }
        } else {
          DAST._IExpression _2188_e = _2177___mcc_h31;
          {
            Dafny.ISequence<Dafny.Rune> _2189_recursiveGen;
            bool _2190_recOwned;
            bool _2191_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2192_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1420;
            bool _out1421;
            bool _out1422;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1423;
            DCOMP.COMP.GenExpr(_2188_e, selfIdent, @params, false, out _out1420, out _out1421, out _out1422, out _out1423);
            _2189_recursiveGen = _out1420;
            _2190_recOwned = _out1421;
            _2191_recErased = _out1422;
            _2192_recIdents = _out1423;
            if (!(_2191_recErased)) {
              Dafny.ISequence<Dafny.Rune> _2193_eraseFn;
              _2193_eraseFn = ((_2190_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2189_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2193_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2189_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), _2189_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").len())"));
            isOwned = true;
            readIdents = _2192_recIdents;
            isErased = true;
          }
        }
      } else if (_source21.is_BinOp) {
        Dafny.ISequence<Dafny.Rune> _2194___mcc_h32 = _source21.dtor_op;
        DAST._IExpression _2195___mcc_h33 = _source21.dtor_left;
        DAST._IExpression _2196___mcc_h34 = _source21.dtor_right;
        DAST._IExpression _2197_r = _2196___mcc_h34;
        DAST._IExpression _2198_l = _2195___mcc_h33;
        Dafny.ISequence<Dafny.Rune> _2199_op = _2194___mcc_h32;
        {
          Dafny.ISequence<Dafny.Rune> _2200_left;
          bool _2201___v80;
          bool _2202_leftErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2203_recIdentsL;
          Dafny.ISequence<Dafny.Rune> _out1424;
          bool _out1425;
          bool _out1426;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1427;
          DCOMP.COMP.GenExpr(_2198_l, selfIdent, @params, true, out _out1424, out _out1425, out _out1426, out _out1427);
          _2200_left = _out1424;
          _2201___v80 = _out1425;
          _2202_leftErased = _out1426;
          _2203_recIdentsL = _out1427;
          Dafny.ISequence<Dafny.Rune> _2204_right;
          bool _2205___v81;
          bool _2206_rightErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2207_recIdentsR;
          Dafny.ISequence<Dafny.Rune> _out1428;
          bool _out1429;
          bool _out1430;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1431;
          DCOMP.COMP.GenExpr(_2197_r, selfIdent, @params, true, out _out1428, out _out1429, out _out1430, out _out1431);
          _2204_right = _out1428;
          _2205___v81 = _out1429;
          _2206_rightErased = _out1430;
          _2207_recIdentsR = _out1431;
          if (!(_2202_leftErased)) {
            _2200_left = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2200_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (!(_2206_rightErased)) {
            _2204_right = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2204_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if ((_2199_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division("), _2200_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _2204_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          } else if ((_2199_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%"))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo("), _2200_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _2204_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2200_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _2199_op), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _2204_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          isOwned = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2203_recIdentsL, _2207_recIdentsR);
          isErased = true;
        }
      } else if (_source21.is_ArrayLen) {
        DAST._IExpression _2208___mcc_h35 = _source21.dtor_expr;
        BigInteger _2209___mcc_h36 = _source21.dtor_dim;
        BigInteger _2210_dim = _2209___mcc_h36;
        DAST._IExpression _2211_expr = _2208___mcc_h35;
        {
          Dafny.ISequence<Dafny.Rune> _2212_recursiveGen;
          bool _2213___v82;
          bool _2214_recErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2215_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1432;
          bool _out1433;
          bool _out1434;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1435;
          DCOMP.COMP.GenExpr(_2211_expr, selfIdent, @params, true, out _out1432, out _out1433, out _out1434, out _out1435);
          _2212_recursiveGen = _out1432;
          _2213___v82 = _out1433;
          _2214_recErased = _out1434;
          _2215_recIdents = _out1435;
          if (!(_2214_recErased)) {
            _2212_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2212_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if ((_2210_dim).Sign == 0) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), _2212_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())"));
          } else {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(m.borrow().len())");
            BigInteger _2216_i;
            _2216_i = BigInteger.One;
            while ((_2216_i) < (_2210_dim)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("m.borrow().get(0).map(|m| "), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"));
              _2216_i = (_2216_i) + (BigInteger.One);
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2212_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow().get(0).map(|m| ")), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"));
          }
          isOwned = true;
          readIdents = _2215_recIdents;
          isErased = true;
        }
      } else if (_source21.is_Select) {
        DAST._IExpression _2217___mcc_h37 = _source21.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _2218___mcc_h38 = _source21.dtor_field;
        bool _2219___mcc_h39 = _source21.dtor_isConstant;
        bool _2220___mcc_h40 = _source21.dtor_onDatatype;
        DAST._IExpression _source73 = _2217___mcc_h37;
        if (_source73.is_Literal) {
          DAST._ILiteral _2221___mcc_h41 = _source73.dtor_Literal_a0;
          bool _2222_isDatatype = _2220___mcc_h40;
          bool _2223_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2224_field = _2218___mcc_h38;
          DAST._IExpression _2225_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2226_onString;
            bool _2227_onOwned;
            bool _2228_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2229_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1436;
            bool _out1437;
            bool _out1438;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1439;
            DCOMP.COMP.GenExpr(_2225_on, selfIdent, @params, false, out _out1436, out _out1437, out _out1438, out _out1439);
            _2226_onString = _out1436;
            _2227_onOwned = _out1437;
            _2228_onErased = _out1438;
            _2229_recIdents = _out1439;
            if (!(_2228_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2230_eraseFn;
              _2230_eraseFn = ((_2227_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2226_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2230_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2226_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2222_isDatatype) || (_2223_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2226_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2224_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2223_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2226_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2224_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2229_recIdents;
          }
        } else if (_source73.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _2231___mcc_h43 = _source73.dtor_Ident_a0;
          bool _2232_isDatatype = _2220___mcc_h40;
          bool _2233_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2234_field = _2218___mcc_h38;
          DAST._IExpression _2235_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2236_onString;
            bool _2237_onOwned;
            bool _2238_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2239_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1440;
            bool _out1441;
            bool _out1442;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1443;
            DCOMP.COMP.GenExpr(_2235_on, selfIdent, @params, false, out _out1440, out _out1441, out _out1442, out _out1443);
            _2236_onString = _out1440;
            _2237_onOwned = _out1441;
            _2238_onErased = _out1442;
            _2239_recIdents = _out1443;
            if (!(_2238_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2240_eraseFn;
              _2240_eraseFn = ((_2237_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2236_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2240_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2236_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2232_isDatatype) || (_2233_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2236_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2234_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2233_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2236_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2234_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2239_recIdents;
          }
        } else if (_source73.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2241___mcc_h45 = _source73.dtor_Companion_a0;
          bool _2242_isDatatype = _2220___mcc_h40;
          bool _2243_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2244_field = _2218___mcc_h38;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2245_c = _2241___mcc_h45;
          {
            Dafny.ISequence<Dafny.Rune> _2246_onString;
            bool _2247_onOwned;
            bool _2248_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2249_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1444;
            bool _out1445;
            bool _out1446;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1447;
            DCOMP.COMP.GenExpr(DAST.Expression.create_Companion(_2245_c), selfIdent, @params, false, out _out1444, out _out1445, out _out1446, out _out1447);
            _2246_onString = _out1444;
            _2247_onOwned = _out1445;
            _2248_onErased = _out1446;
            _2249_recIdents = _out1447;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2246_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _2244_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
            isOwned = true;
            isErased = false;
            readIdents = _2249_recIdents;
          }
        } else if (_source73.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _2250___mcc_h47 = _source73.dtor_Tuple_a0;
          bool _2251_isDatatype = _2220___mcc_h40;
          bool _2252_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2253_field = _2218___mcc_h38;
          DAST._IExpression _2254_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2255_onString;
            bool _2256_onOwned;
            bool _2257_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2258_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1448;
            bool _out1449;
            bool _out1450;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1451;
            DCOMP.COMP.GenExpr(_2254_on, selfIdent, @params, false, out _out1448, out _out1449, out _out1450, out _out1451);
            _2255_onString = _out1448;
            _2256_onOwned = _out1449;
            _2257_onErased = _out1450;
            _2258_recIdents = _out1451;
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
        } else if (_source73.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2260___mcc_h49 = _source73.dtor_path;
          Dafny.ISequence<DAST._IExpression> _2261___mcc_h50 = _source73.dtor_args;
          bool _2262_isDatatype = _2220___mcc_h40;
          bool _2263_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2264_field = _2218___mcc_h38;
          DAST._IExpression _2265_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2266_onString;
            bool _2267_onOwned;
            bool _2268_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2269_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1452;
            bool _out1453;
            bool _out1454;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1455;
            DCOMP.COMP.GenExpr(_2265_on, selfIdent, @params, false, out _out1452, out _out1453, out _out1454, out _out1455);
            _2266_onString = _out1452;
            _2267_onOwned = _out1453;
            _2268_onErased = _out1454;
            _2269_recIdents = _out1455;
            if (!(_2268_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2270_eraseFn;
              _2270_eraseFn = ((_2267_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2266_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2270_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2266_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2262_isDatatype) || (_2263_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2266_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2264_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2263_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2266_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2264_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2269_recIdents;
          }
        } else if (_source73.is_NewArray) {
          Dafny.ISequence<DAST._IExpression> _2271___mcc_h53 = _source73.dtor_dims;
          bool _2272_isDatatype = _2220___mcc_h40;
          bool _2273_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2274_field = _2218___mcc_h38;
          DAST._IExpression _2275_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2276_onString;
            bool _2277_onOwned;
            bool _2278_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2279_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1456;
            bool _out1457;
            bool _out1458;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1459;
            DCOMP.COMP.GenExpr(_2275_on, selfIdent, @params, false, out _out1456, out _out1457, out _out1458, out _out1459);
            _2276_onString = _out1456;
            _2277_onOwned = _out1457;
            _2278_onErased = _out1458;
            _2279_recIdents = _out1459;
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
        } else if (_source73.is_DatatypeValue) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2281___mcc_h55 = _source73.dtor_path;
          Dafny.ISequence<Dafny.Rune> _2282___mcc_h56 = _source73.dtor_variant;
          bool _2283___mcc_h57 = _source73.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2284___mcc_h58 = _source73.dtor_contents;
          bool _2285_isDatatype = _2220___mcc_h40;
          bool _2286_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2287_field = _2218___mcc_h38;
          DAST._IExpression _2288_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2289_onString;
            bool _2290_onOwned;
            bool _2291_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2292_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1460;
            bool _out1461;
            bool _out1462;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1463;
            DCOMP.COMP.GenExpr(_2288_on, selfIdent, @params, false, out _out1460, out _out1461, out _out1462, out _out1463);
            _2289_onString = _out1460;
            _2290_onOwned = _out1461;
            _2291_onErased = _out1462;
            _2292_recIdents = _out1463;
            if (!(_2291_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2293_eraseFn;
              _2293_eraseFn = ((_2290_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2289_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2293_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2289_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2285_isDatatype) || (_2286_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2289_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2287_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2286_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2289_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2287_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2292_recIdents;
          }
        } else if (_source73.is_Convert) {
          DAST._IExpression _2294___mcc_h63 = _source73.dtor_value;
          DAST._IType _2295___mcc_h64 = _source73.dtor_from;
          DAST._IType _2296___mcc_h65 = _source73.dtor_typ;
          bool _2297_isDatatype = _2220___mcc_h40;
          bool _2298_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2299_field = _2218___mcc_h38;
          DAST._IExpression _2300_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2301_onString;
            bool _2302_onOwned;
            bool _2303_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2304_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1464;
            bool _out1465;
            bool _out1466;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1467;
            DCOMP.COMP.GenExpr(_2300_on, selfIdent, @params, false, out _out1464, out _out1465, out _out1466, out _out1467);
            _2301_onString = _out1464;
            _2302_onOwned = _out1465;
            _2303_onErased = _out1466;
            _2304_recIdents = _out1467;
            if (!(_2303_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2305_eraseFn;
              _2305_eraseFn = ((_2302_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2301_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2305_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2301_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2297_isDatatype) || (_2298_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2301_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2299_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2298_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2301_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2299_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2304_recIdents;
          }
        } else if (_source73.is_SeqConstruct) {
          DAST._IExpression _2306___mcc_h69 = _source73.dtor_length;
          DAST._IExpression _2307___mcc_h70 = _source73.dtor_elem;
          bool _2308_isDatatype = _2220___mcc_h40;
          bool _2309_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2310_field = _2218___mcc_h38;
          DAST._IExpression _2311_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2312_onString;
            bool _2313_onOwned;
            bool _2314_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2315_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1468;
            bool _out1469;
            bool _out1470;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1471;
            DCOMP.COMP.GenExpr(_2311_on, selfIdent, @params, false, out _out1468, out _out1469, out _out1470, out _out1471);
            _2312_onString = _out1468;
            _2313_onOwned = _out1469;
            _2314_onErased = _out1470;
            _2315_recIdents = _out1471;
            if (!(_2314_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2316_eraseFn;
              _2316_eraseFn = ((_2313_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2312_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2316_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2312_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2308_isDatatype) || (_2309_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2312_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2310_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2309_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2312_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2310_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2315_recIdents;
          }
        } else if (_source73.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _2317___mcc_h73 = _source73.dtor_elements;
          bool _2318_isDatatype = _2220___mcc_h40;
          bool _2319_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2320_field = _2218___mcc_h38;
          DAST._IExpression _2321_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2322_onString;
            bool _2323_onOwned;
            bool _2324_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2325_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1472;
            bool _out1473;
            bool _out1474;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1475;
            DCOMP.COMP.GenExpr(_2321_on, selfIdent, @params, false, out _out1472, out _out1473, out _out1474, out _out1475);
            _2322_onString = _out1472;
            _2323_onOwned = _out1473;
            _2324_onErased = _out1474;
            _2325_recIdents = _out1475;
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
        } else if (_source73.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _2327___mcc_h75 = _source73.dtor_elements;
          bool _2328_isDatatype = _2220___mcc_h40;
          bool _2329_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2330_field = _2218___mcc_h38;
          DAST._IExpression _2331_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2332_onString;
            bool _2333_onOwned;
            bool _2334_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2335_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1476;
            bool _out1477;
            bool _out1478;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1479;
            DCOMP.COMP.GenExpr(_2331_on, selfIdent, @params, false, out _out1476, out _out1477, out _out1478, out _out1479);
            _2332_onString = _out1476;
            _2333_onOwned = _out1477;
            _2334_onErased = _out1478;
            _2335_recIdents = _out1479;
            if (!(_2334_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2336_eraseFn;
              _2336_eraseFn = ((_2333_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2332_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2336_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2332_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2328_isDatatype) || (_2329_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2332_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2330_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2329_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2332_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2330_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2335_recIdents;
          }
        } else if (_source73.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2337___mcc_h77 = _source73.dtor_mapElems;
          bool _2338_isDatatype = _2220___mcc_h40;
          bool _2339_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2340_field = _2218___mcc_h38;
          DAST._IExpression _2341_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2342_onString;
            bool _2343_onOwned;
            bool _2344_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2345_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1480;
            bool _out1481;
            bool _out1482;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1483;
            DCOMP.COMP.GenExpr(_2341_on, selfIdent, @params, false, out _out1480, out _out1481, out _out1482, out _out1483);
            _2342_onString = _out1480;
            _2343_onOwned = _out1481;
            _2344_onErased = _out1482;
            _2345_recIdents = _out1483;
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
        } else if (_source73.is_This) {
          bool _2347_isDatatype = _2220___mcc_h40;
          bool _2348_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2349_field = _2218___mcc_h38;
          DAST._IExpression _2350_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2351_onString;
            bool _2352_onOwned;
            bool _2353_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2354_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1484;
            bool _out1485;
            bool _out1486;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1487;
            DCOMP.COMP.GenExpr(_2350_on, selfIdent, @params, false, out _out1484, out _out1485, out _out1486, out _out1487);
            _2351_onString = _out1484;
            _2352_onOwned = _out1485;
            _2353_onErased = _out1486;
            _2354_recIdents = _out1487;
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
        } else if (_source73.is_Ite) {
          DAST._IExpression _2356___mcc_h79 = _source73.dtor_cond;
          DAST._IExpression _2357___mcc_h80 = _source73.dtor_thn;
          DAST._IExpression _2358___mcc_h81 = _source73.dtor_els;
          bool _2359_isDatatype = _2220___mcc_h40;
          bool _2360_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2361_field = _2218___mcc_h38;
          DAST._IExpression _2362_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2363_onString;
            bool _2364_onOwned;
            bool _2365_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2366_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1488;
            bool _out1489;
            bool _out1490;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1491;
            DCOMP.COMP.GenExpr(_2362_on, selfIdent, @params, false, out _out1488, out _out1489, out _out1490, out _out1491);
            _2363_onString = _out1488;
            _2364_onOwned = _out1489;
            _2365_onErased = _out1490;
            _2366_recIdents = _out1491;
            if (!(_2365_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2367_eraseFn;
              _2367_eraseFn = ((_2364_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2363_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2367_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2363_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2359_isDatatype) || (_2360_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2363_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2361_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2360_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2363_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2361_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2366_recIdents;
          }
        } else if (_source73.is_UnOp) {
          DAST._IUnaryOp _2368___mcc_h85 = _source73.dtor_unOp;
          DAST._IExpression _2369___mcc_h86 = _source73.dtor_expr;
          bool _2370_isDatatype = _2220___mcc_h40;
          bool _2371_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2372_field = _2218___mcc_h38;
          DAST._IExpression _2373_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2374_onString;
            bool _2375_onOwned;
            bool _2376_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2377_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1492;
            bool _out1493;
            bool _out1494;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1495;
            DCOMP.COMP.GenExpr(_2373_on, selfIdent, @params, false, out _out1492, out _out1493, out _out1494, out _out1495);
            _2374_onString = _out1492;
            _2375_onOwned = _out1493;
            _2376_onErased = _out1494;
            _2377_recIdents = _out1495;
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
        } else if (_source73.is_BinOp) {
          Dafny.ISequence<Dafny.Rune> _2379___mcc_h89 = _source73.dtor_op;
          DAST._IExpression _2380___mcc_h90 = _source73.dtor_left;
          DAST._IExpression _2381___mcc_h91 = _source73.dtor_right;
          bool _2382_isDatatype = _2220___mcc_h40;
          bool _2383_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2384_field = _2218___mcc_h38;
          DAST._IExpression _2385_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2386_onString;
            bool _2387_onOwned;
            bool _2388_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2389_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1496;
            bool _out1497;
            bool _out1498;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1499;
            DCOMP.COMP.GenExpr(_2385_on, selfIdent, @params, false, out _out1496, out _out1497, out _out1498, out _out1499);
            _2386_onString = _out1496;
            _2387_onOwned = _out1497;
            _2388_onErased = _out1498;
            _2389_recIdents = _out1499;
            if (!(_2388_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2390_eraseFn;
              _2390_eraseFn = ((_2387_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2386_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2390_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2386_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2382_isDatatype) || (_2383_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2386_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2384_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2383_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2386_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2384_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2389_recIdents;
          }
        } else if (_source73.is_ArrayLen) {
          DAST._IExpression _2391___mcc_h95 = _source73.dtor_expr;
          BigInteger _2392___mcc_h96 = _source73.dtor_dim;
          bool _2393_isDatatype = _2220___mcc_h40;
          bool _2394_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2395_field = _2218___mcc_h38;
          DAST._IExpression _2396_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2397_onString;
            bool _2398_onOwned;
            bool _2399_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2400_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1500;
            bool _out1501;
            bool _out1502;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1503;
            DCOMP.COMP.GenExpr(_2396_on, selfIdent, @params, false, out _out1500, out _out1501, out _out1502, out _out1503);
            _2397_onString = _out1500;
            _2398_onOwned = _out1501;
            _2399_onErased = _out1502;
            _2400_recIdents = _out1503;
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
        } else if (_source73.is_Select) {
          DAST._IExpression _2402___mcc_h99 = _source73.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2403___mcc_h100 = _source73.dtor_field;
          bool _2404___mcc_h101 = _source73.dtor_isConstant;
          bool _2405___mcc_h102 = _source73.dtor_onDatatype;
          bool _2406_isDatatype = _2220___mcc_h40;
          bool _2407_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2408_field = _2218___mcc_h38;
          DAST._IExpression _2409_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2410_onString;
            bool _2411_onOwned;
            bool _2412_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2413_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1504;
            bool _out1505;
            bool _out1506;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1507;
            DCOMP.COMP.GenExpr(_2409_on, selfIdent, @params, false, out _out1504, out _out1505, out _out1506, out _out1507);
            _2410_onString = _out1504;
            _2411_onOwned = _out1505;
            _2412_onErased = _out1506;
            _2413_recIdents = _out1507;
            if (!(_2412_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2414_eraseFn;
              _2414_eraseFn = ((_2411_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2410_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2414_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2410_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2406_isDatatype) || (_2407_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2410_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2408_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2407_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2410_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2408_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2413_recIdents;
          }
        } else if (_source73.is_SelectFn) {
          DAST._IExpression _2415___mcc_h107 = _source73.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2416___mcc_h108 = _source73.dtor_field;
          bool _2417___mcc_h109 = _source73.dtor_onDatatype;
          bool _2418___mcc_h110 = _source73.dtor_isStatic;
          BigInteger _2419___mcc_h111 = _source73.dtor_arity;
          bool _2420_isDatatype = _2220___mcc_h40;
          bool _2421_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2422_field = _2218___mcc_h38;
          DAST._IExpression _2423_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2424_onString;
            bool _2425_onOwned;
            bool _2426_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2427_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1508;
            bool _out1509;
            bool _out1510;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1511;
            DCOMP.COMP.GenExpr(_2423_on, selfIdent, @params, false, out _out1508, out _out1509, out _out1510, out _out1511);
            _2424_onString = _out1508;
            _2425_onOwned = _out1509;
            _2426_onErased = _out1510;
            _2427_recIdents = _out1511;
            if (!(_2426_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2428_eraseFn;
              _2428_eraseFn = ((_2425_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2424_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2428_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2424_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2420_isDatatype) || (_2421_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2424_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2422_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2421_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2424_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2422_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2427_recIdents;
          }
        } else if (_source73.is_Index) {
          DAST._IExpression _2429___mcc_h117 = _source73.dtor_expr;
          DAST._ICollKind _2430___mcc_h118 = _source73.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2431___mcc_h119 = _source73.dtor_indices;
          bool _2432_isDatatype = _2220___mcc_h40;
          bool _2433_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2434_field = _2218___mcc_h38;
          DAST._IExpression _2435_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2436_onString;
            bool _2437_onOwned;
            bool _2438_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2439_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1512;
            bool _out1513;
            bool _out1514;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1515;
            DCOMP.COMP.GenExpr(_2435_on, selfIdent, @params, false, out _out1512, out _out1513, out _out1514, out _out1515);
            _2436_onString = _out1512;
            _2437_onOwned = _out1513;
            _2438_onErased = _out1514;
            _2439_recIdents = _out1515;
            if (!(_2438_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2440_eraseFn;
              _2440_eraseFn = ((_2437_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2436_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2440_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2436_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2432_isDatatype) || (_2433_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2436_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2434_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2433_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2436_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2434_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2439_recIdents;
          }
        } else if (_source73.is_IndexRange) {
          DAST._IExpression _2441___mcc_h123 = _source73.dtor_expr;
          bool _2442___mcc_h124 = _source73.dtor_isArray;
          DAST._IOptional<DAST._IExpression> _2443___mcc_h125 = _source73.dtor_low;
          DAST._IOptional<DAST._IExpression> _2444___mcc_h126 = _source73.dtor_high;
          bool _2445_isDatatype = _2220___mcc_h40;
          bool _2446_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2447_field = _2218___mcc_h38;
          DAST._IExpression _2448_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2449_onString;
            bool _2450_onOwned;
            bool _2451_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2452_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1516;
            bool _out1517;
            bool _out1518;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1519;
            DCOMP.COMP.GenExpr(_2448_on, selfIdent, @params, false, out _out1516, out _out1517, out _out1518, out _out1519);
            _2449_onString = _out1516;
            _2450_onOwned = _out1517;
            _2451_onErased = _out1518;
            _2452_recIdents = _out1519;
            if (!(_2451_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2453_eraseFn;
              _2453_eraseFn = ((_2450_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2449_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2453_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2449_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2445_isDatatype) || (_2446_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2449_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2447_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2446_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2449_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2447_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2452_recIdents;
          }
        } else if (_source73.is_TupleSelect) {
          DAST._IExpression _2454___mcc_h131 = _source73.dtor_expr;
          BigInteger _2455___mcc_h132 = _source73.dtor_index;
          bool _2456_isDatatype = _2220___mcc_h40;
          bool _2457_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2458_field = _2218___mcc_h38;
          DAST._IExpression _2459_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2460_onString;
            bool _2461_onOwned;
            bool _2462_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2463_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1520;
            bool _out1521;
            bool _out1522;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1523;
            DCOMP.COMP.GenExpr(_2459_on, selfIdent, @params, false, out _out1520, out _out1521, out _out1522, out _out1523);
            _2460_onString = _out1520;
            _2461_onOwned = _out1521;
            _2462_onErased = _out1522;
            _2463_recIdents = _out1523;
            if (!(_2462_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2464_eraseFn;
              _2464_eraseFn = ((_2461_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2460_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2464_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2460_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2456_isDatatype) || (_2457_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2460_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2458_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2457_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2460_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2458_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2463_recIdents;
          }
        } else if (_source73.is_Call) {
          DAST._IExpression _2465___mcc_h135 = _source73.dtor_on;
          Dafny.ISequence<Dafny.Rune> _2466___mcc_h136 = _source73.dtor_name;
          Dafny.ISequence<DAST._IType> _2467___mcc_h137 = _source73.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2468___mcc_h138 = _source73.dtor_args;
          bool _2469_isDatatype = _2220___mcc_h40;
          bool _2470_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2471_field = _2218___mcc_h38;
          DAST._IExpression _2472_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2473_onString;
            bool _2474_onOwned;
            bool _2475_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2476_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1524;
            bool _out1525;
            bool _out1526;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1527;
            DCOMP.COMP.GenExpr(_2472_on, selfIdent, @params, false, out _out1524, out _out1525, out _out1526, out _out1527);
            _2473_onString = _out1524;
            _2474_onOwned = _out1525;
            _2475_onErased = _out1526;
            _2476_recIdents = _out1527;
            if (!(_2475_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2477_eraseFn;
              _2477_eraseFn = ((_2474_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2473_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2477_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2473_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2469_isDatatype) || (_2470_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2473_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2471_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2470_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2473_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2471_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2476_recIdents;
          }
        } else if (_source73.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2478___mcc_h143 = _source73.dtor_params;
          DAST._IType _2479___mcc_h144 = _source73.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2480___mcc_h145 = _source73.dtor_body;
          bool _2481_isDatatype = _2220___mcc_h40;
          bool _2482_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2483_field = _2218___mcc_h38;
          DAST._IExpression _2484_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2485_onString;
            bool _2486_onOwned;
            bool _2487_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2488_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1528;
            bool _out1529;
            bool _out1530;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1531;
            DCOMP.COMP.GenExpr(_2484_on, selfIdent, @params, false, out _out1528, out _out1529, out _out1530, out _out1531);
            _2485_onString = _out1528;
            _2486_onOwned = _out1529;
            _2487_onErased = _out1530;
            _2488_recIdents = _out1531;
            if (!(_2487_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2489_eraseFn;
              _2489_eraseFn = ((_2486_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2485_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2489_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2485_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2481_isDatatype) || (_2482_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2485_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2483_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2482_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2485_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2483_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2488_recIdents;
          }
        } else if (_source73.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2490___mcc_h149 = _source73.dtor_values;
          DAST._IType _2491___mcc_h150 = _source73.dtor_retType;
          DAST._IExpression _2492___mcc_h151 = _source73.dtor_expr;
          bool _2493_isDatatype = _2220___mcc_h40;
          bool _2494_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2495_field = _2218___mcc_h38;
          DAST._IExpression _2496_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2497_onString;
            bool _2498_onOwned;
            bool _2499_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2500_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1532;
            bool _out1533;
            bool _out1534;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1535;
            DCOMP.COMP.GenExpr(_2496_on, selfIdent, @params, false, out _out1532, out _out1533, out _out1534, out _out1535);
            _2497_onString = _out1532;
            _2498_onOwned = _out1533;
            _2499_onErased = _out1534;
            _2500_recIdents = _out1535;
            if (!(_2499_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2501_eraseFn;
              _2501_eraseFn = ((_2498_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2497_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2501_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2497_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2493_isDatatype) || (_2494_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2497_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2495_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2494_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2497_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2495_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2500_recIdents;
          }
        } else if (_source73.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2502___mcc_h155 = _source73.dtor_name;
          DAST._IType _2503___mcc_h156 = _source73.dtor_typ;
          DAST._IExpression _2504___mcc_h157 = _source73.dtor_value;
          DAST._IExpression _2505___mcc_h158 = _source73.dtor_iifeBody;
          bool _2506_isDatatype = _2220___mcc_h40;
          bool _2507_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2508_field = _2218___mcc_h38;
          DAST._IExpression _2509_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2510_onString;
            bool _2511_onOwned;
            bool _2512_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2513_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1536;
            bool _out1537;
            bool _out1538;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1539;
            DCOMP.COMP.GenExpr(_2509_on, selfIdent, @params, false, out _out1536, out _out1537, out _out1538, out _out1539);
            _2510_onString = _out1536;
            _2511_onOwned = _out1537;
            _2512_onErased = _out1538;
            _2513_recIdents = _out1539;
            if (!(_2512_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2514_eraseFn;
              _2514_eraseFn = ((_2511_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2510_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2514_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2510_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2506_isDatatype) || (_2507_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2510_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2508_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2507_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2510_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2508_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2513_recIdents;
          }
        } else if (_source73.is_Apply) {
          DAST._IExpression _2515___mcc_h163 = _source73.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2516___mcc_h164 = _source73.dtor_args;
          bool _2517_isDatatype = _2220___mcc_h40;
          bool _2518_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2519_field = _2218___mcc_h38;
          DAST._IExpression _2520_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2521_onString;
            bool _2522_onOwned;
            bool _2523_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2524_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1540;
            bool _out1541;
            bool _out1542;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1543;
            DCOMP.COMP.GenExpr(_2520_on, selfIdent, @params, false, out _out1540, out _out1541, out _out1542, out _out1543);
            _2521_onString = _out1540;
            _2522_onOwned = _out1541;
            _2523_onErased = _out1542;
            _2524_recIdents = _out1543;
            if (!(_2523_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2525_eraseFn;
              _2525_eraseFn = ((_2522_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2521_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2525_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2521_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2517_isDatatype) || (_2518_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2521_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2519_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2518_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2521_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2519_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2524_recIdents;
          }
        } else if (_source73.is_TypeTest) {
          DAST._IExpression _2526___mcc_h167 = _source73.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2527___mcc_h168 = _source73.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2528___mcc_h169 = _source73.dtor_variant;
          bool _2529_isDatatype = _2220___mcc_h40;
          bool _2530_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2531_field = _2218___mcc_h38;
          DAST._IExpression _2532_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2533_onString;
            bool _2534_onOwned;
            bool _2535_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2536_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1544;
            bool _out1545;
            bool _out1546;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1547;
            DCOMP.COMP.GenExpr(_2532_on, selfIdent, @params, false, out _out1544, out _out1545, out _out1546, out _out1547);
            _2533_onString = _out1544;
            _2534_onOwned = _out1545;
            _2535_onErased = _out1546;
            _2536_recIdents = _out1547;
            if (!(_2535_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2537_eraseFn;
              _2537_eraseFn = ((_2534_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2533_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2537_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2533_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2529_isDatatype) || (_2530_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2533_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2531_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2530_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2533_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2531_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2536_recIdents;
          }
        } else if (_source73.is_InitializationValue) {
          DAST._IType _2538___mcc_h173 = _source73.dtor_typ;
          bool _2539_isDatatype = _2220___mcc_h40;
          bool _2540_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2541_field = _2218___mcc_h38;
          DAST._IExpression _2542_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2543_onString;
            bool _2544_onOwned;
            bool _2545_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2546_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1548;
            bool _out1549;
            bool _out1550;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1551;
            DCOMP.COMP.GenExpr(_2542_on, selfIdent, @params, false, out _out1548, out _out1549, out _out1550, out _out1551);
            _2543_onString = _out1548;
            _2544_onOwned = _out1549;
            _2545_onErased = _out1550;
            _2546_recIdents = _out1551;
            if (!(_2545_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2547_eraseFn;
              _2547_eraseFn = ((_2544_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2543_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2547_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2543_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2539_isDatatype) || (_2540_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2543_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2541_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2540_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2543_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2541_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2546_recIdents;
          }
        } else if (_source73.is_BoolBoundedPool) {
          bool _2548_isDatatype = _2220___mcc_h40;
          bool _2549_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2550_field = _2218___mcc_h38;
          DAST._IExpression _2551_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2552_onString;
            bool _2553_onOwned;
            bool _2554_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2555_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1552;
            bool _out1553;
            bool _out1554;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1555;
            DCOMP.COMP.GenExpr(_2551_on, selfIdent, @params, false, out _out1552, out _out1553, out _out1554, out _out1555);
            _2552_onString = _out1552;
            _2553_onOwned = _out1553;
            _2554_onErased = _out1554;
            _2555_recIdents = _out1555;
            if (!(_2554_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2556_eraseFn;
              _2556_eraseFn = ((_2553_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2552_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2556_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2552_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2548_isDatatype) || (_2549_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2552_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2550_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2549_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2552_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2550_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2555_recIdents;
          }
        } else {
          DAST._IExpression _2557___mcc_h175 = _source73.dtor_lo;
          DAST._IExpression _2558___mcc_h176 = _source73.dtor_hi;
          bool _2559_isDatatype = _2220___mcc_h40;
          bool _2560_isConstant = _2219___mcc_h39;
          Dafny.ISequence<Dafny.Rune> _2561_field = _2218___mcc_h38;
          DAST._IExpression _2562_on = _2217___mcc_h37;
          {
            Dafny.ISequence<Dafny.Rune> _2563_onString;
            bool _2564_onOwned;
            bool _2565_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2566_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1556;
            bool _out1557;
            bool _out1558;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1559;
            DCOMP.COMP.GenExpr(_2562_on, selfIdent, @params, false, out _out1556, out _out1557, out _out1558, out _out1559);
            _2563_onString = _out1556;
            _2564_onOwned = _out1557;
            _2565_onErased = _out1558;
            _2566_recIdents = _out1559;
            if (!(_2565_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2567_eraseFn;
              _2567_eraseFn = ((_2564_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2563_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2567_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2563_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2559_isDatatype) || (_2560_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2563_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2561_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2560_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2563_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2561_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2566_recIdents;
          }
        }
      } else if (_source21.is_SelectFn) {
        DAST._IExpression _2568___mcc_h179 = _source21.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _2569___mcc_h180 = _source21.dtor_field;
        bool _2570___mcc_h181 = _source21.dtor_onDatatype;
        bool _2571___mcc_h182 = _source21.dtor_isStatic;
        BigInteger _2572___mcc_h183 = _source21.dtor_arity;
        BigInteger _2573_arity = _2572___mcc_h183;
        bool _2574_isStatic = _2571___mcc_h182;
        bool _2575_isDatatype = _2570___mcc_h181;
        Dafny.ISequence<Dafny.Rune> _2576_field = _2569___mcc_h180;
        DAST._IExpression _2577_on = _2568___mcc_h179;
        {
          Dafny.ISequence<Dafny.Rune> _2578_onString;
          bool _2579_onOwned;
          bool _2580___v83;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2581_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1560;
          bool _out1561;
          bool _out1562;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1563;
          DCOMP.COMP.GenExpr(_2577_on, selfIdent, @params, false, out _out1560, out _out1561, out _out1562, out _out1563);
          _2578_onString = _out1560;
          _2579_onOwned = _out1561;
          _2580___v83 = _out1562;
          _2581_recIdents = _out1563;
          if (_2574_isStatic) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2578_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _2576_field);
          } else {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2578_onString), ((_2579_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            Dafny.ISequence<Dafny.Rune> _2582_args;
            _2582_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            BigInteger _2583_i;
            _2583_i = BigInteger.Zero;
            while ((_2583_i) < (_2573_arity)) {
              if ((_2583_i).Sign == 1) {
                _2582_args = Dafny.Sequence<Dafny.Rune>.Concat(_2582_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2582_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2582_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), DCOMP.__default.natToString(_2583_i));
              _2583_i = (_2583_i) + (BigInteger.One);
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2582_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), _2576_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2582_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper(::std::rc::Rc::new("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
          isErased = false;
          readIdents = _2581_recIdents;
        }
      } else if (_source21.is_Index) {
        DAST._IExpression _2584___mcc_h184 = _source21.dtor_expr;
        DAST._ICollKind _2585___mcc_h185 = _source21.dtor_collKind;
        Dafny.ISequence<DAST._IExpression> _2586___mcc_h186 = _source21.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _2587_indices = _2586___mcc_h186;
        DAST._ICollKind _2588_collKind = _2585___mcc_h185;
        DAST._IExpression _2589_on = _2584___mcc_h184;
        {
          Dafny.ISequence<Dafny.Rune> _2590_onString;
          bool _2591_onOwned;
          bool _2592_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2593_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1564;
          bool _out1565;
          bool _out1566;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1567;
          DCOMP.COMP.GenExpr(_2589_on, selfIdent, @params, false, out _out1564, out _out1565, out _out1566, out _out1567);
          _2590_onString = _out1564;
          _2591_onOwned = _out1565;
          _2592_onErased = _out1566;
          _2593_recIdents = _out1567;
          readIdents = _2593_recIdents;
          if (!(_2592_onErased)) {
            Dafny.ISequence<Dafny.Rune> _2594_eraseFn;
            _2594_eraseFn = ((_2591_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _2590_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2594_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2590_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          s = _2590_onString;
          BigInteger _2595_i;
          _2595_i = BigInteger.Zero;
          while ((_2595_i) < (new BigInteger((_2587_indices).Count))) {
            if (object.Equals(_2588_collKind, DAST.CollKind.create_Array())) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow()"));
            }
            if (object.Equals(_2588_collKind, DAST.CollKind.create_Map())) {
              Dafny.ISequence<Dafny.Rune> _2596_idx;
              bool _2597_idxOwned;
              bool _2598_idxErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2599_recIdentsIdx;
              Dafny.ISequence<Dafny.Rune> _out1568;
              bool _out1569;
              bool _out1570;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1571;
              DCOMP.COMP.GenExpr((_2587_indices).Select(_2595_i), selfIdent, @params, false, out _out1568, out _out1569, out _out1570, out _out1571);
              _2596_idx = _out1568;
              _2597_idxOwned = _out1569;
              _2598_idxErased = _out1570;
              _2599_recIdentsIdx = _out1571;
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")[")), ((_2597_idxOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _2596_idx), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2599_recIdentsIdx);
            } else {
              Dafny.ISequence<Dafny.Rune> _2600_idx;
              bool _2601___v84;
              bool _2602_idxErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2603_recIdentsIdx;
              Dafny.ISequence<Dafny.Rune> _out1572;
              bool _out1573;
              bool _out1574;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1575;
              DCOMP.COMP.GenExpr((_2587_indices).Select(_2595_i), selfIdent, @params, true, out _out1572, out _out1573, out _out1574, out _out1575);
              _2600_idx = _out1572;
              _2601___v84 = _out1573;
              _2602_idxErased = _out1574;
              _2603_recIdentsIdx = _out1575;
              if (!(_2602_idxErased)) {
                _2600_idx = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2600_idx), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")[<usize as ::dafny_runtime::NumCast>::from(")), _2600_idx), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2603_recIdentsIdx);
            }
            _2595_i = (_2595_i) + (BigInteger.One);
          }
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
            isOwned = true;
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(&"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = false;
          }
          isErased = _2592_onErased;
        }
      } else if (_source21.is_IndexRange) {
        DAST._IExpression _2604___mcc_h187 = _source21.dtor_expr;
        bool _2605___mcc_h188 = _source21.dtor_isArray;
        DAST._IOptional<DAST._IExpression> _2606___mcc_h189 = _source21.dtor_low;
        DAST._IOptional<DAST._IExpression> _2607___mcc_h190 = _source21.dtor_high;
        DAST._IOptional<DAST._IExpression> _2608_high = _2607___mcc_h190;
        DAST._IOptional<DAST._IExpression> _2609_low = _2606___mcc_h189;
        bool _2610_isArray = _2605___mcc_h188;
        DAST._IExpression _2611_on = _2604___mcc_h187;
        {
          Dafny.ISequence<Dafny.Rune> _2612_onString;
          bool _2613_onOwned;
          bool _2614_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2615_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1576;
          bool _out1577;
          bool _out1578;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1579;
          DCOMP.COMP.GenExpr(_2611_on, selfIdent, @params, false, out _out1576, out _out1577, out _out1578, out _out1579);
          _2612_onString = _out1576;
          _2613_onOwned = _out1577;
          _2614_onErased = _out1578;
          _2615_recIdents = _out1579;
          readIdents = _2615_recIdents;
          if (!(_2614_onErased)) {
            Dafny.ISequence<Dafny.Rune> _2616_eraseFn;
            _2616_eraseFn = ((_2613_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _2612_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2616_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2612_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          s = _2612_onString;
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _2617_lowString;
          _2617_lowString = DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None();
          DAST._IOptional<DAST._IExpression> _source74 = _2609_low;
          if (_source74.is_Some) {
            DAST._IExpression _2618___mcc_h1128 = _source74.dtor_Some_a0;
            DAST._IExpression _2619_l = _2618___mcc_h1128;
            {
              Dafny.ISequence<Dafny.Rune> _2620_lString;
              bool _2621___v85;
              bool _2622_lErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2623_recIdentsL;
              Dafny.ISequence<Dafny.Rune> _out1580;
              bool _out1581;
              bool _out1582;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1583;
              DCOMP.COMP.GenExpr(_2619_l, selfIdent, @params, true, out _out1580, out _out1581, out _out1582, out _out1583);
              _2620_lString = _out1580;
              _2621___v85 = _out1581;
              _2622_lErased = _out1582;
              _2623_recIdentsL = _out1583;
              if (!(_2622_lErased)) {
                _2620_lString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2620_lString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _2617_lowString = DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_Some(_2620_lString);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2623_recIdentsL);
            }
          } else {
          }
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _2624_highString;
          _2624_highString = DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None();
          DAST._IOptional<DAST._IExpression> _source75 = _2608_high;
          if (_source75.is_Some) {
            DAST._IExpression _2625___mcc_h1129 = _source75.dtor_Some_a0;
            DAST._IExpression _2626_h = _2625___mcc_h1129;
            {
              Dafny.ISequence<Dafny.Rune> _2627_hString;
              bool _2628___v86;
              bool _2629_hErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2630_recIdentsH;
              Dafny.ISequence<Dafny.Rune> _out1584;
              bool _out1585;
              bool _out1586;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1587;
              DCOMP.COMP.GenExpr(_2626_h, selfIdent, @params, true, out _out1584, out _out1585, out _out1586, out _out1587);
              _2627_hString = _out1584;
              _2628___v86 = _out1585;
              _2629_hErased = _out1586;
              _2630_recIdentsH = _out1587;
              if (!(_2629_hErased)) {
                _2627_hString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2627_hString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _2624_highString = DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_Some(_2627_hString);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2630_recIdentsH);
            }
          } else {
          }
          if (_2610_isArray) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow()"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[")), ((System.Func<DAST._IOptional<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>)((_source76) => {
            if (_source76.is_Some) {
              Dafny.ISequence<Dafny.Rune> _2631___mcc_h1130 = _source76.dtor_Some_a0;
              return Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_2631___mcc_h1130, _pat_let0_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_pat_let0_0, _2632_l => Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<usize as ::dafny_runtime::NumCast>::from("), _2632_l), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"))));
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            }
          }))(_2617_lowString)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("..")), ((System.Func<DAST._IOptional<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>)((_source77) => {
            if (_source77.is_Some) {
              Dafny.ISequence<Dafny.Rune> _2633___mcc_h1131 = _source77.dtor_Some_a0;
              return Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_2633___mcc_h1131, _pat_let1_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_pat_let1_0, _2634_h => Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<usize as ::dafny_runtime::NumCast>::from("), _2634_h), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"))));
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            }
          }))(_2624_highString)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
          isErased = _2614_onErased;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".to_vec())"));
          isOwned = true;
        }
      } else if (_source21.is_TupleSelect) {
        DAST._IExpression _2635___mcc_h191 = _source21.dtor_expr;
        BigInteger _2636___mcc_h192 = _source21.dtor_index;
        BigInteger _2637_idx = _2636___mcc_h192;
        DAST._IExpression _2638_on = _2635___mcc_h191;
        {
          Dafny.ISequence<Dafny.Rune> _2639_onString;
          bool _2640___v87;
          bool _2641_tupErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2642_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1588;
          bool _out1589;
          bool _out1590;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1591;
          DCOMP.COMP.GenExpr(_2638_on, selfIdent, @params, false, out _out1588, out _out1589, out _out1590, out _out1591);
          _2639_onString = _out1588;
          _2640___v87 = _out1589;
          _2641_tupErased = _out1590;
          _2642_recIdents = _out1591;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2639_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").")), DCOMP.__default.natToString(_2637_idx));
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
            isOwned = true;
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
            isOwned = false;
          }
          isErased = _2641_tupErased;
          readIdents = _2642_recIdents;
        }
      } else if (_source21.is_Call) {
        DAST._IExpression _2643___mcc_h193 = _source21.dtor_on;
        Dafny.ISequence<Dafny.Rune> _2644___mcc_h194 = _source21.dtor_name;
        Dafny.ISequence<DAST._IType> _2645___mcc_h195 = _source21.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _2646___mcc_h196 = _source21.dtor_args;
        Dafny.ISequence<DAST._IExpression> _2647_args = _2646___mcc_h196;
        Dafny.ISequence<DAST._IType> _2648_typeArgs = _2645___mcc_h195;
        Dafny.ISequence<Dafny.Rune> _2649_name = _2644___mcc_h194;
        DAST._IExpression _2650_on = _2643___mcc_h193;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _2651_typeArgString;
          _2651_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_2648_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _2652_typeI;
            _2652_typeI = BigInteger.Zero;
            _2651_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<");
            while ((_2652_typeI) < (new BigInteger((_2648_typeArgs).Count))) {
              if ((_2652_typeI).Sign == 1) {
                _2651_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_2651_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _2653_typeString;
              Dafny.ISequence<Dafny.Rune> _out1592;
              _out1592 = DCOMP.COMP.GenType((_2648_typeArgs).Select(_2652_typeI), false, false);
              _2653_typeString = _out1592;
              _2651_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_2651_typeArgString, _2653_typeString);
              _2652_typeI = (_2652_typeI) + (BigInteger.One);
            }
            _2651_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_2651_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
          Dafny.ISequence<Dafny.Rune> _2654_argString;
          _2654_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _2655_i;
          _2655_i = BigInteger.Zero;
          while ((_2655_i) < (new BigInteger((_2647_args).Count))) {
            if ((_2655_i).Sign == 1) {
              _2654_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2654_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2656_argExpr;
            bool _2657_isOwned;
            bool _2658_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2659_argIdents;
            Dafny.ISequence<Dafny.Rune> _out1593;
            bool _out1594;
            bool _out1595;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1596;
            DCOMP.COMP.GenExpr((_2647_args).Select(_2655_i), selfIdent, @params, false, out _out1593, out _out1594, out _out1595, out _out1596);
            _2656_argExpr = _out1593;
            _2657_isOwned = _out1594;
            _2658_argErased = _out1595;
            _2659_argIdents = _out1596;
            if (_2657_isOwned) {
              _2656_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2656_argExpr);
            }
            _2654_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2654_argString, _2656_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2659_argIdents);
            _2655_i = (_2655_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2660_enclosingString;
          bool _2661___v88;
          bool _2662___v89;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2663_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1597;
          bool _out1598;
          bool _out1599;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1600;
          DCOMP.COMP.GenExpr(_2650_on, selfIdent, @params, false, out _out1597, out _out1598, out _out1599, out _out1600);
          _2660_enclosingString = _out1597;
          _2661___v88 = _out1598;
          _2662___v89 = _out1599;
          _2663_recIdents = _out1600;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2663_recIdents);
          DAST._IExpression _source78 = _2650_on;
          if (_source78.is_Literal) {
            DAST._ILiteral _2664___mcc_h1132 = _source78.dtor_Literal_a0;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _2665___mcc_h1134 = _source78.dtor_Ident_a0;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2666___mcc_h1136 = _source78.dtor_Companion_a0;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2660_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), (_2649_name));
            }
          } else if (_source78.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _2667___mcc_h1138 = _source78.dtor_Tuple_a0;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2668___mcc_h1140 = _source78.dtor_path;
            Dafny.ISequence<DAST._IExpression> _2669___mcc_h1141 = _source78.dtor_args;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _2670___mcc_h1144 = _source78.dtor_dims;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2671___mcc_h1146 = _source78.dtor_path;
            Dafny.ISequence<Dafny.Rune> _2672___mcc_h1147 = _source78.dtor_variant;
            bool _2673___mcc_h1148 = _source78.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2674___mcc_h1149 = _source78.dtor_contents;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_Convert) {
            DAST._IExpression _2675___mcc_h1154 = _source78.dtor_value;
            DAST._IType _2676___mcc_h1155 = _source78.dtor_from;
            DAST._IType _2677___mcc_h1156 = _source78.dtor_typ;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_SeqConstruct) {
            DAST._IExpression _2678___mcc_h1160 = _source78.dtor_length;
            DAST._IExpression _2679___mcc_h1161 = _source78.dtor_elem;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _2680___mcc_h1164 = _source78.dtor_elements;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _2681___mcc_h1166 = _source78.dtor_elements;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_MapValue) {
            Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2682___mcc_h1168 = _source78.dtor_mapElems;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_This) {
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_Ite) {
            DAST._IExpression _2683___mcc_h1170 = _source78.dtor_cond;
            DAST._IExpression _2684___mcc_h1171 = _source78.dtor_thn;
            DAST._IExpression _2685___mcc_h1172 = _source78.dtor_els;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_UnOp) {
            DAST._IUnaryOp _2686___mcc_h1176 = _source78.dtor_unOp;
            DAST._IExpression _2687___mcc_h1177 = _source78.dtor_expr;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_BinOp) {
            Dafny.ISequence<Dafny.Rune> _2688___mcc_h1180 = _source78.dtor_op;
            DAST._IExpression _2689___mcc_h1181 = _source78.dtor_left;
            DAST._IExpression _2690___mcc_h1182 = _source78.dtor_right;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_ArrayLen) {
            DAST._IExpression _2691___mcc_h1186 = _source78.dtor_expr;
            BigInteger _2692___mcc_h1187 = _source78.dtor_dim;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_Select) {
            DAST._IExpression _2693___mcc_h1190 = _source78.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2694___mcc_h1191 = _source78.dtor_field;
            bool _2695___mcc_h1192 = _source78.dtor_isConstant;
            bool _2696___mcc_h1193 = _source78.dtor_onDatatype;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_SelectFn) {
            DAST._IExpression _2697___mcc_h1198 = _source78.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2698___mcc_h1199 = _source78.dtor_field;
            bool _2699___mcc_h1200 = _source78.dtor_onDatatype;
            bool _2700___mcc_h1201 = _source78.dtor_isStatic;
            BigInteger _2701___mcc_h1202 = _source78.dtor_arity;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_Index) {
            DAST._IExpression _2702___mcc_h1208 = _source78.dtor_expr;
            DAST._ICollKind _2703___mcc_h1209 = _source78.dtor_collKind;
            Dafny.ISequence<DAST._IExpression> _2704___mcc_h1210 = _source78.dtor_indices;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_IndexRange) {
            DAST._IExpression _2705___mcc_h1214 = _source78.dtor_expr;
            bool _2706___mcc_h1215 = _source78.dtor_isArray;
            DAST._IOptional<DAST._IExpression> _2707___mcc_h1216 = _source78.dtor_low;
            DAST._IOptional<DAST._IExpression> _2708___mcc_h1217 = _source78.dtor_high;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_TupleSelect) {
            DAST._IExpression _2709___mcc_h1222 = _source78.dtor_expr;
            BigInteger _2710___mcc_h1223 = _source78.dtor_index;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_Call) {
            DAST._IExpression _2711___mcc_h1226 = _source78.dtor_on;
            Dafny.ISequence<Dafny.Rune> _2712___mcc_h1227 = _source78.dtor_name;
            Dafny.ISequence<DAST._IType> _2713___mcc_h1228 = _source78.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _2714___mcc_h1229 = _source78.dtor_args;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2715___mcc_h1234 = _source78.dtor_params;
            DAST._IType _2716___mcc_h1235 = _source78.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _2717___mcc_h1236 = _source78.dtor_body;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2718___mcc_h1240 = _source78.dtor_values;
            DAST._IType _2719___mcc_h1241 = _source78.dtor_retType;
            DAST._IExpression _2720___mcc_h1242 = _source78.dtor_expr;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _2721___mcc_h1246 = _source78.dtor_name;
            DAST._IType _2722___mcc_h1247 = _source78.dtor_typ;
            DAST._IExpression _2723___mcc_h1248 = _source78.dtor_value;
            DAST._IExpression _2724___mcc_h1249 = _source78.dtor_iifeBody;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_Apply) {
            DAST._IExpression _2725___mcc_h1254 = _source78.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _2726___mcc_h1255 = _source78.dtor_args;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_TypeTest) {
            DAST._IExpression _2727___mcc_h1258 = _source78.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2728___mcc_h1259 = _source78.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _2729___mcc_h1260 = _source78.dtor_variant;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_InitializationValue) {
            DAST._IType _2730___mcc_h1264 = _source78.dtor_typ;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else if (_source78.is_BoolBoundedPool) {
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          } else {
            DAST._IExpression _2731___mcc_h1266 = _source78.dtor_lo;
            DAST._IExpression _2732___mcc_h1267 = _source78.dtor_hi;
            {
              _2660_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2660_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2649_name));
            }
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2660_enclosingString, _2651_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2654_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = false;
        }
      } else if (_source21.is_Lambda) {
        Dafny.ISequence<DAST._IFormal> _2733___mcc_h197 = _source21.dtor_params;
        DAST._IType _2734___mcc_h198 = _source21.dtor_retType;
        Dafny.ISequence<DAST._IStatement> _2735___mcc_h199 = _source21.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2736_body = _2735___mcc_h199;
        DAST._IType _2737_retType = _2734___mcc_h198;
        Dafny.ISequence<DAST._IFormal> _2738_params = _2733___mcc_h197;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2739_paramNames;
          _2739_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2740_i;
          _2740_i = BigInteger.Zero;
          while ((_2740_i) < (new BigInteger((_2738_params).Count))) {
            _2739_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2739_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(((_2738_params).Select(_2740_i)).dtor_name));
            _2740_i = (_2740_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2741_recursiveGen;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2742_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1601;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1602;
          DCOMP.COMP.GenStmts(_2736_body, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None(), _2739_paramNames, true, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), out _out1601, out _out1602);
          _2741_recursiveGen = _out1601;
          _2742_recIdents = _out1602;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _2743_allReadCloned;
          _2743_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          while (!(_2742_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
            Dafny.ISequence<Dafny.Rune> _2744_next;
            foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_1 in (_2742_recIdents).Elements) {
              _2744_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_1;
              if ((_2742_recIdents).Contains(_2744_next)) {
                goto after__ASSIGN_SUCH_THAT_1;
              }
            }
            throw new System.Exception("assign-such-that search produced no value (line 1826)");
          after__ASSIGN_SUCH_THAT_1:;
            if (!((_2739_paramNames).Contains(_2744_next))) {
              _2743_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2743_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), _2744_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _2744_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2744_next));
            }
            _2742_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2742_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2744_next));
          }
          Dafny.ISequence<Dafny.Rune> _2745_paramsString;
          _2745_paramsString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          Dafny.ISequence<Dafny.Rune> _2746_paramTypes;
          _2746_paramTypes = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          _2740_i = BigInteger.Zero;
          while ((_2740_i) < (new BigInteger((_2738_params).Count))) {
            if ((_2740_i).Sign == 1) {
              _2745_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(_2745_paramsString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              _2746_paramTypes = Dafny.Sequence<Dafny.Rune>.Concat(_2746_paramTypes, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2747_typStr;
            Dafny.ISequence<Dafny.Rune> _out1603;
            _out1603 = DCOMP.COMP.GenType(((_2738_params).Select(_2740_i)).dtor_typ, false, true);
            _2747_typStr = _out1603;
            _2745_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2745_paramsString, ((_2738_params).Select(_2740_i)).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": &")), _2747_typStr);
            _2746_paramTypes = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2746_paramTypes, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")), _2747_typStr);
            _2740_i = (_2740_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2748_retTypeGen;
          Dafny.ISequence<Dafny.Rune> _out1604;
          _out1604 = DCOMP.COMP.GenType(_2737_retType, false, true);
          _2748_retTypeGen = _out1604;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper::<::std::rc::Rc<dyn Fn("), _2746_paramTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), _2748_retTypeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>({\n")), _2743_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(move |")), _2745_paramsString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| -> ")), _2748_retTypeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _2741_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})})"));
          isOwned = true;
          isErased = false;
        }
      } else if (_source21.is_BetaRedex) {
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2749___mcc_h200 = _source21.dtor_values;
        DAST._IType _2750___mcc_h201 = _source21.dtor_retType;
        DAST._IExpression _2751___mcc_h202 = _source21.dtor_expr;
        DAST._IExpression _2752_expr = _2751___mcc_h202;
        DAST._IType _2753_retType = _2750___mcc_h201;
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2754_values = _2749___mcc_h200;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2755_paramNames;
          _2755_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2756_paramNamesSet;
          _2756_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2757_i;
          _2757_i = BigInteger.Zero;
          while ((_2757_i) < (new BigInteger((_2754_values).Count))) {
            _2755_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2755_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((((_2754_values).Select(_2757_i)).dtor__0).dtor_name));
            _2756_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2756_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((((_2754_values).Select(_2757_i)).dtor__0).dtor_name));
            _2757_i = (_2757_i) + (BigInteger.One);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          Dafny.ISequence<Dafny.Rune> _2758_paramsString;
          _2758_paramsString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          _2757_i = BigInteger.Zero;
          while ((_2757_i) < (new BigInteger((_2754_values).Count))) {
            if ((_2757_i).Sign == 1) {
              _2758_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(_2758_paramsString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2759_typStr;
            Dafny.ISequence<Dafny.Rune> _out1605;
            _out1605 = DCOMP.COMP.GenType((((_2754_values).Select(_2757_i)).dtor__0).dtor_typ, false, true);
            _2759_typStr = _out1605;
            Dafny.ISequence<Dafny.Rune> _2760_valueGen;
            bool _2761___v92;
            bool _2762_valueErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2763_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1606;
            bool _out1607;
            bool _out1608;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1609;
            DCOMP.COMP.GenExpr(((_2754_values).Select(_2757_i)).dtor__1, selfIdent, @params, true, out _out1606, out _out1607, out _out1608, out _out1609);
            _2760_valueGen = _out1606;
            _2761___v92 = _out1607;
            _2762_valueErased = _out1608;
            _2763_recIdents = _out1609;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), (((_2754_values).Select(_2757_i)).dtor__0).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _2759_typStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2763_recIdents);
            if (_2762_valueErased) {
              _2760_valueGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2760_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _2760_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            _2757_i = (_2757_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2764_recGen;
          bool _2765_recOwned;
          bool _2766_recErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2767_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1610;
          bool _out1611;
          bool _out1612;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1613;
          DCOMP.COMP.GenExpr(_2752_expr, selfIdent, _2755_paramNames, mustOwn, out _out1610, out _out1611, out _out1612, out _out1613);
          _2764_recGen = _out1610;
          _2765_recOwned = _out1611;
          _2766_recErased = _out1612;
          _2767_recIdents = _out1613;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2767_recIdents, _2756_paramNamesSet);
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _2764_recGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
          isOwned = _2765_recOwned;
          isErased = _2766_recErased;
        }
      } else if (_source21.is_IIFE) {
        Dafny.ISequence<Dafny.Rune> _2768___mcc_h203 = _source21.dtor_name;
        DAST._IType _2769___mcc_h204 = _source21.dtor_typ;
        DAST._IExpression _2770___mcc_h205 = _source21.dtor_value;
        DAST._IExpression _2771___mcc_h206 = _source21.dtor_iifeBody;
        DAST._IExpression _2772_iifeBody = _2771___mcc_h206;
        DAST._IExpression _2773_value = _2770___mcc_h205;
        DAST._IType _2774_tpe = _2769___mcc_h204;
        Dafny.ISequence<Dafny.Rune> _2775_name = _2768___mcc_h203;
        {
          Dafny.ISequence<Dafny.Rune> _2776_valueGen;
          bool _2777___v93;
          bool _2778_valueErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2779_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1614;
          bool _out1615;
          bool _out1616;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1617;
          DCOMP.COMP.GenExpr(_2773_value, selfIdent, @params, true, out _out1614, out _out1615, out _out1616, out _out1617);
          _2776_valueGen = _out1614;
          _2777___v93 = _out1615;
          _2778_valueErased = _out1616;
          _2779_recIdents = _out1617;
          if (_2778_valueErased) {
            _2776_valueGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2776_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          readIdents = _2779_recIdents;
          Dafny.ISequence<Dafny.Rune> _2780_valueTypeGen;
          Dafny.ISequence<Dafny.Rune> _out1618;
          _out1618 = DCOMP.COMP.GenType(_2774_tpe, false, true);
          _2780_valueTypeGen = _out1618;
          Dafny.ISequence<Dafny.Rune> _2781_bodyGen;
          bool _2782___v94;
          bool _2783_bodyErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2784_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out1619;
          bool _out1620;
          bool _out1621;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1622;
          DCOMP.COMP.GenExpr(_2772_iifeBody, selfIdent, @params, true, out _out1619, out _out1620, out _out1621, out _out1622);
          _2781_bodyGen = _out1619;
          _2782___v94 = _out1620;
          _2783_bodyErased = _out1621;
          _2784_bodyIdents = _out1622;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2784_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_2775_name))));
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet r#"), (_2775_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _2780_valueTypeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _2776_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n")), _2781_bodyGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
          isOwned = true;
          isErased = _2783_bodyErased;
        }
      } else if (_source21.is_Apply) {
        DAST._IExpression _2785___mcc_h207 = _source21.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _2786___mcc_h208 = _source21.dtor_args;
        Dafny.ISequence<DAST._IExpression> _2787_args = _2786___mcc_h208;
        DAST._IExpression _2788_func = _2785___mcc_h207;
        {
          Dafny.ISequence<Dafny.Rune> _2789_funcString;
          bool _2790___v95;
          bool _2791_funcErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2792_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1623;
          bool _out1624;
          bool _out1625;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1626;
          DCOMP.COMP.GenExpr(_2788_func, selfIdent, @params, false, out _out1623, out _out1624, out _out1625, out _out1626);
          _2789_funcString = _out1623;
          _2790___v95 = _out1624;
          _2791_funcErased = _out1625;
          _2792_recIdents = _out1626;
          readIdents = _2792_recIdents;
          Dafny.ISequence<Dafny.Rune> _2793_argString;
          _2793_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _2794_i;
          _2794_i = BigInteger.Zero;
          while ((_2794_i) < (new BigInteger((_2787_args).Count))) {
            if ((_2794_i).Sign == 1) {
              _2793_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2793_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2795_argExpr;
            bool _2796_isOwned;
            bool _2797_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2798_argIdents;
            Dafny.ISequence<Dafny.Rune> _out1627;
            bool _out1628;
            bool _out1629;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1630;
            DCOMP.COMP.GenExpr((_2787_args).Select(_2794_i), selfIdent, @params, false, out _out1627, out _out1628, out _out1629, out _out1630);
            _2795_argExpr = _out1627;
            _2796_isOwned = _out1628;
            _2797_argErased = _out1629;
            _2798_argIdents = _out1630;
            if (_2796_isOwned) {
              _2795_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2795_argExpr);
            }
            _2793_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2793_argString, _2795_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2798_argIdents);
            _2794_i = (_2794_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), _2789_funcString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2793_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
          isErased = false;
        }
      } else if (_source21.is_TypeTest) {
        DAST._IExpression _2799___mcc_h209 = _source21.dtor_on;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2800___mcc_h210 = _source21.dtor_dType;
        Dafny.ISequence<Dafny.Rune> _2801___mcc_h211 = _source21.dtor_variant;
        Dafny.ISequence<Dafny.Rune> _2802_variant = _2801___mcc_h211;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2803_dType = _2800___mcc_h210;
        DAST._IExpression _2804_on = _2799___mcc_h209;
        {
          Dafny.ISequence<Dafny.Rune> _2805_exprGen;
          bool _2806___v96;
          bool _2807_exprErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2808_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1631;
          bool _out1632;
          bool _out1633;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1634;
          DCOMP.COMP.GenExpr(_2804_on, selfIdent, @params, false, out _out1631, out _out1632, out _out1633, out _out1634);
          _2805_exprGen = _out1631;
          _2806___v96 = _out1632;
          _2807_exprErased = _out1633;
          _2808_recIdents = _out1634;
          Dafny.ISequence<Dafny.Rune> _2809_dTypePath;
          Dafny.ISequence<Dafny.Rune> _out1635;
          _out1635 = DCOMP.COMP.GenPath(_2803_dType);
          _2809_dTypePath = _out1635;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!("), _2805_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref(), ")), _2809_dTypePath), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _2802_variant), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. })"));
          isOwned = true;
          isErased = true;
          readIdents = _2808_recIdents;
        }
      } else if (_source21.is_InitializationValue) {
        DAST._IType _2810___mcc_h212 = _source21.dtor_typ;
        DAST._IType _2811_typ = _2810___mcc_h212;
        {
          Dafny.ISequence<Dafny.Rune> _2812_typString;
          Dafny.ISequence<Dafny.Rune> _out1636;
          _out1636 = DCOMP.COMP.GenType(_2811_typ, false, false);
          _2812_typString = _out1636;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2812_typString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()"));
          isOwned = true;
          isErased = false;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source21.is_BoolBoundedPool) {
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]");
          isOwned = true;
          isErased = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else {
        DAST._IExpression _2813___mcc_h213 = _source21.dtor_lo;
        DAST._IExpression _2814___mcc_h214 = _source21.dtor_hi;
        DAST._IExpression _2815_hi = _2814___mcc_h214;
        DAST._IExpression _2816_lo = _2813___mcc_h213;
        {
          Dafny.ISequence<Dafny.Rune> _2817_loString;
          bool _2818___v97;
          bool _2819_loErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2820_recIdentsLo;
          Dafny.ISequence<Dafny.Rune> _out1637;
          bool _out1638;
          bool _out1639;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1640;
          DCOMP.COMP.GenExpr(_2816_lo, selfIdent, @params, true, out _out1637, out _out1638, out _out1639, out _out1640);
          _2817_loString = _out1637;
          _2818___v97 = _out1638;
          _2819_loErased = _out1639;
          _2820_recIdentsLo = _out1640;
          Dafny.ISequence<Dafny.Rune> _2821_hiString;
          bool _2822___v98;
          bool _2823_hiErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2824_recIdentsHi;
          Dafny.ISequence<Dafny.Rune> _out1641;
          bool _out1642;
          bool _out1643;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1644;
          DCOMP.COMP.GenExpr(_2815_hi, selfIdent, @params, true, out _out1641, out _out1642, out _out1643, out _out1644);
          _2821_hiString = _out1641;
          _2822___v98 = _out1642;
          _2823_hiErased = _out1643;
          _2824_recIdentsHi = _out1644;
          if (!(_2819_loErased)) {
            _2817_loString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2817_loString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (!(_2823_hiErased)) {
            _2821_hiString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2821_hiString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::integer_range("), _2817_loString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _2821_hiString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2820_recIdentsLo, _2824_recIdentsHi);
        }
      }
    }
    public static Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern crate dafny_runtime;\n"));
      BigInteger _2825_i;
      _2825_i = BigInteger.Zero;
      while ((_2825_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _2826_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        Dafny.ISequence<Dafny.Rune> _out1645;
        _out1645 = DCOMP.COMP.GenModule((p).Select(_2825_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2826_generated = _out1645;
        if ((_2825_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2826_generated);
        _2825_i = (_2825_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2827_i;
      _2827_i = BigInteger.Zero;
      while ((_2827_i) < (new BigInteger((fullName).Count))) {
        if ((_2827_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (fullName).Select(_2827_i));
        _2827_i = (_2827_i) + (BigInteger.One);
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("();\n}"));
      return s;
    }
  }
} // end of namespace DCOMP

