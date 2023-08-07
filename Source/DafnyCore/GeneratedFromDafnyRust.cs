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

  public interface _INewtype {
    bool is_Newtype { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    DAST._IType dtor_base { get; }
    _INewtype DowncastClone();
  }
  public class Newtype : _INewtype {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly DAST._IType _base;
    public Newtype(Dafny.ISequence<Dafny.Rune> name, DAST._IType @base) {
      this._name = name;
      this._base = @base;
    }
    public _INewtype DowncastClone() {
      if (this is _INewtype dt) { return dt; }
      return new Newtype(_name, _base);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Newtype;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._base, oth._base);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._base));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Newtype.Newtype";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._base);
      s += ")";
      return s;
    }
    private static readonly DAST._INewtype theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, DAST.Type.Default());
    public static DAST._INewtype Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._INewtype> _TYPE = new Dafny.TypeDescriptor<DAST._INewtype>(DAST.Newtype.Default());
    public static Dafny.TypeDescriptor<DAST._INewtype> _TypeDescriptor() {
      return _TYPE;
    }
    public static _INewtype create(Dafny.ISequence<Dafny.Rune> name, DAST._IType @base) {
      return new Newtype(name, @base);
    }
    public static _INewtype create_Newtype(Dafny.ISequence<Dafny.Rune> name, DAST._IType @base) {
      return create(name, @base);
    }
    public bool is_Newtype { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public DAST._IType dtor_base {
      get {
        return this._base;
      }
    }
  }

  public interface _IType {
    bool is_Path { get; }
    bool is_Tuple { get; }
    bool is_Primitive { get; }
    bool is_Passthrough { get; }
    bool is_TypeArg { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_Path_a0 { get; }
    Dafny.ISequence<DAST._IType> dtor_typeArgs { get; }
    DAST._IResolvedType dtor_resolved { get; }
    Dafny.ISequence<DAST._IType> dtor_Tuple_a0 { get; }
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
      hash = ((hash << 5) + hash) + 2;
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
      hash = ((hash << 5) + hash) + 3;
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
      hash = ((hash << 5) + hash) + 4;
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
    bool is_String { get; }
    bool is_Bool { get; }
    bool is_Char { get; }
    _IPrimitive DowncastClone();
  }
  public abstract class Primitive : _IPrimitive {
    public Primitive() {
    }
    private static readonly DAST._IPrimitive theDefault = create_String();
    public static DAST._IPrimitive Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IPrimitive> _TYPE = new Dafny.TypeDescriptor<DAST._IPrimitive>(DAST.Primitive.Default());
    public static Dafny.TypeDescriptor<DAST._IPrimitive> _TypeDescriptor() {
      return _TYPE;
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
    public bool is_String { get { return this is Primitive_String; } }
    public bool is_Bool { get { return this is Primitive_Bool; } }
    public bool is_Char { get { return this is Primitive_Char; } }
    public static System.Collections.Generic.IEnumerable<_IPrimitive> AllSingletonConstructors {
      get {
        yield return Primitive.create_String();
        yield return Primitive.create_Bool();
        yield return Primitive.create_Char();
      }
    }
    public abstract _IPrimitive DowncastClone();
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
      hash = ((hash << 5) + hash) + 0;
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
      hash = ((hash << 5) + hash) + 1;
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
      hash = ((hash << 5) + hash) + 2;
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
    public static _IResolvedType create_Newtype() {
      return new ResolvedType_Newtype();
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
    public ResolvedType_Newtype() : base() {
    }
    public override _IResolvedType DowncastClone() {
      if (this is _IResolvedType dt) { return dt; }
      return new ResolvedType_Newtype();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ResolvedType_Newtype;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.ResolvedType.Newtype";
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
    Dafny.ISequence<DAST._IType> dtor_superClasses { get; }
    Dafny.ISequence<DAST._IClassItem> dtor_body { get; }
    _IClass DowncastClone();
  }
  public class Class : _IClass {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<DAST._IType> _superClasses;
    public readonly Dafny.ISequence<DAST._IClassItem> _body;
    public Class(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> superClasses, Dafny.ISequence<DAST._IClassItem> body) {
      this._name = name;
      this._superClasses = superClasses;
      this._body = body;
    }
    public _IClass DowncastClone() {
      if (this is _IClass dt) { return dt; }
      return new Class(_name, _superClasses, _body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Class;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._superClasses, oth._superClasses) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._superClasses));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Class.Class";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._superClasses);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
    private static readonly DAST._IClass theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._IType>.Empty, Dafny.Sequence<DAST._IClassItem>.Empty);
    public static DAST._IClass Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IClass> _TYPE = new Dafny.TypeDescriptor<DAST._IClass>(DAST.Class.Default());
    public static Dafny.TypeDescriptor<DAST._IClass> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IClass create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> superClasses, Dafny.ISequence<DAST._IClassItem> body) {
      return new Class(name, superClasses, body);
    }
    public static _IClass create_Class(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> superClasses, Dafny.ISequence<DAST._IClassItem> body) {
      return create(name, superClasses, body);
    }
    public bool is_Class { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_superClasses {
      get {
        return this._superClasses;
      }
    }
    public Dafny.ISequence<DAST._IClassItem> dtor_body {
      get {
        return this._body;
      }
    }
  }

  public interface _ITrait {
    bool is_Trait { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<DAST._IType> dtor_typeParams { get; }
    Dafny.ISequence<DAST._IClassItem> dtor_body { get; }
    _ITrait DowncastClone();
  }
  public class Trait : _ITrait {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<DAST._IType> _typeParams;
    public readonly Dafny.ISequence<DAST._IClassItem> _body;
    public Trait(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IClassItem> body) {
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
    private static readonly DAST._ITrait theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._IType>.Empty, Dafny.Sequence<DAST._IClassItem>.Empty);
    public static DAST._ITrait Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._ITrait> _TYPE = new Dafny.TypeDescriptor<DAST._ITrait>(DAST.Trait.Default());
    public static Dafny.TypeDescriptor<DAST._ITrait> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITrait create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IClassItem> body) {
      return new Trait(name, typeParams, body);
    }
    public static _ITrait create_Trait(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IClassItem> body) {
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
    public Dafny.ISequence<DAST._IClassItem> dtor_body {
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
    Dafny.ISequence<DAST._IClassItem> dtor_body { get; }
    bool dtor_isCo { get; }
    _IDatatype DowncastClone();
  }
  public class Datatype : _IDatatype {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<Dafny.Rune> _enclosingModule;
    public readonly Dafny.ISequence<DAST._IType> _typeParams;
    public readonly Dafny.ISequence<DAST._IDatatypeCtor> _ctors;
    public readonly Dafny.ISequence<DAST._IClassItem> _body;
    public readonly bool _isCo;
    public Datatype(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IDatatypeCtor> ctors, Dafny.ISequence<DAST._IClassItem> body, bool isCo) {
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
    private static readonly DAST._IDatatype theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._IType>.Empty, Dafny.Sequence<DAST._IDatatypeCtor>.Empty, Dafny.Sequence<DAST._IClassItem>.Empty, false);
    public static DAST._IDatatype Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IDatatype> _TYPE = new Dafny.TypeDescriptor<DAST._IDatatype>(DAST.Datatype.Default());
    public static Dafny.TypeDescriptor<DAST._IDatatype> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDatatype create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IDatatypeCtor> ctors, Dafny.ISequence<DAST._IClassItem> body, bool isCo) {
      return new Datatype(name, enclosingModule, typeParams, ctors, body, isCo);
    }
    public static _IDatatype create_Datatype(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IDatatypeCtor> ctors, Dafny.ISequence<DAST._IClassItem> body, bool isCo) {
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
    public Dafny.ISequence<DAST._IClassItem> dtor_body {
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

  public interface _IClassItem {
    bool is_Method { get; }
    bool is_Field { get; }
    DAST._IMethod dtor_Method_a0 { get; }
    DAST._IFormal dtor_Field_a0 { get; }
    _IClassItem DowncastClone();
  }
  public abstract class ClassItem : _IClassItem {
    public ClassItem() {
    }
    private static readonly DAST._IClassItem theDefault = create_Method(DAST.Method.Default());
    public static DAST._IClassItem Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IClassItem> _TYPE = new Dafny.TypeDescriptor<DAST._IClassItem>(DAST.ClassItem.Default());
    public static Dafny.TypeDescriptor<DAST._IClassItem> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IClassItem create_Method(DAST._IMethod _a0) {
      return new ClassItem_Method(_a0);
    }
    public static _IClassItem create_Field(DAST._IFormal _a0) {
      return new ClassItem_Field(_a0);
    }
    public bool is_Method { get { return this is ClassItem_Method; } }
    public bool is_Field { get { return this is ClassItem_Field; } }
    public DAST._IMethod dtor_Method_a0 {
      get {
        var d = this;
        return ((ClassItem_Method)d)._a0;
      }
    }
    public DAST._IFormal dtor_Field_a0 {
      get {
        var d = this;
        return ((ClassItem_Field)d)._a0;
      }
    }
    public abstract _IClassItem DowncastClone();
  }
  public class ClassItem_Method : ClassItem {
    public readonly DAST._IMethod _a0;
    public ClassItem_Method(DAST._IMethod _a0) : base() {
      this._a0 = _a0;
    }
    public override _IClassItem DowncastClone() {
      if (this is _IClassItem dt) { return dt; }
      return new ClassItem_Method(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ClassItem_Method;
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
  }
  public class ClassItem_Field : ClassItem {
    public readonly DAST._IFormal _a0;
    public ClassItem_Field(DAST._IFormal _a0) : base() {
      this._a0 = _a0;
    }
    public override _IClassItem DowncastClone() {
      if (this is _IClassItem dt) { return dt; }
      return new ClassItem_Field(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ClassItem_Field;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.ClassItem.Field";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
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
    public static _IStatement create_Assign(Dafny.ISequence<Dafny.Rune> name, DAST._IExpression @value) {
      return new Statement_Assign(name, @value);
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
        if (d is Statement_Assign) { return ((Statement_Assign)d)._name; }
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
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly DAST._IExpression _value;
    public Statement_Assign(Dafny.ISequence<Dafny.Rune> name, DAST._IExpression @value) : base() {
      this._name = name;
      this._value = @value;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_Assign(_name, _value);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_Assign;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Assign";
      s += "(";
      s += this._name.ToVerbatimString(true);
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

  public interface _IExpression {
    bool is_Literal { get; }
    bool is_Ident { get; }
    bool is_Companion { get; }
    bool is_Tuple { get; }
    bool is_New { get; }
    bool is_DatatypeValue { get; }
    bool is_This { get; }
    bool is_Ite { get; }
    bool is_UnOp { get; }
    bool is_BinOp { get; }
    bool is_Select { get; }
    bool is_TupleSelect { get; }
    bool is_Call { get; }
    bool is_TypeTest { get; }
    bool is_InitializationValue { get; }
    DAST._ILiteral dtor_Literal_a0 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_Ident_a0 { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_Companion_a0 { get; }
    Dafny.ISequence<DAST._IExpression> dtor_Tuple_a0 { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_path { get; }
    Dafny.ISequence<DAST._IExpression> dtor_args { get; }
    Dafny.ISequence<Dafny.Rune> dtor_variant { get; }
    bool dtor_isCo { get; }
    Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> dtor_contents { get; }
    DAST._IExpression dtor_cond { get; }
    DAST._IExpression dtor_thn { get; }
    DAST._IExpression dtor_els { get; }
    DAST._IUnaryOp dtor_unOp { get; }
    DAST._IExpression dtor_expr { get; }
    Dafny.ISequence<Dafny.Rune> dtor_op { get; }
    DAST._IExpression dtor_left { get; }
    DAST._IExpression dtor_right { get; }
    Dafny.ISequence<Dafny.Rune> dtor_field { get; }
    bool dtor_onDatatype { get; }
    BigInteger dtor_index { get; }
    DAST._IExpression dtor_on { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<DAST._IType> dtor_typeArgs { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_dType { get; }
    DAST._IType dtor_typ { get; }
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
    public static _IExpression create_DatatypeValue(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path, Dafny.ISequence<Dafny.Rune> variant, bool isCo, Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> contents) {
      return new Expression_DatatypeValue(path, variant, isCo, contents);
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
    public static _IExpression create_Select(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, bool onDatatype) {
      return new Expression_Select(expr, field, onDatatype);
    }
    public static _IExpression create_TupleSelect(DAST._IExpression expr, BigInteger index) {
      return new Expression_TupleSelect(expr, index);
    }
    public static _IExpression create_Call(DAST._IExpression @on, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args) {
      return new Expression_Call(@on, name, typeArgs, args);
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
    public bool is_DatatypeValue { get { return this is Expression_DatatypeValue; } }
    public bool is_This { get { return this is Expression_This; } }
    public bool is_Ite { get { return this is Expression_Ite; } }
    public bool is_UnOp { get { return this is Expression_UnOp; } }
    public bool is_BinOp { get { return this is Expression_BinOp; } }
    public bool is_Select { get { return this is Expression_Select; } }
    public bool is_TupleSelect { get { return this is Expression_TupleSelect; } }
    public bool is_Call { get { return this is Expression_Call; } }
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
        return ((Expression_Call)d)._args;
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
        return ((Expression_TupleSelect)d)._expr;
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
        return ((Expression_Select)d)._field;
      }
    }
    public bool dtor_onDatatype {
      get {
        var d = this;
        return ((Expression_Select)d)._onDatatype;
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
        return ((Expression_Call)d)._name;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_typeArgs {
      get {
        var d = this;
        return ((Expression_Call)d)._typeArgs;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_dType {
      get {
        var d = this;
        return ((Expression_TypeTest)d)._dType;
      }
    }
    public DAST._IType dtor_typ {
      get {
        var d = this;
        return ((Expression_InitializationValue)d)._typ;
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
      hash = ((hash << 5) + hash) + 5;
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
      hash = ((hash << 5) + hash) + 6;
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
      hash = ((hash << 5) + hash) + 7;
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
      hash = ((hash << 5) + hash) + 8;
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
      hash = ((hash << 5) + hash) + 9;
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
    public readonly bool _onDatatype;
    public Expression_Select(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, bool onDatatype) : base() {
      this._expr = expr;
      this._field = field;
      this._onDatatype = onDatatype;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Select(_expr, _field, _onDatatype);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Select;
      return oth != null && object.Equals(this._expr, oth._expr) && object.Equals(this._field, oth._field) && this._onDatatype == oth._onDatatype;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 10;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._field));
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
      s += Dafny.Helpers.ToString(this._onDatatype);
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
      hash = ((hash << 5) + hash) + 11;
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
      hash = ((hash << 5) + hash) + 12;
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
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeArgs);
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
      hash = ((hash << 5) + hash) + 13;
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
      hash = ((hash << 5) + hash) + 14;
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
    bool dtor_BoolLiteral_a0 { get; }
    BigInteger dtor_IntLiteral_a0 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_DecLiteral_a0 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_StringLiteral_a0 { get; }
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
    public static _ILiteral create_IntLiteral(BigInteger _a0) {
      return new Literal_IntLiteral(_a0);
    }
    public static _ILiteral create_DecLiteral(Dafny.ISequence<Dafny.Rune> _a0) {
      return new Literal_DecLiteral(_a0);
    }
    public static _ILiteral create_StringLiteral(Dafny.ISequence<Dafny.Rune> _a0) {
      return new Literal_StringLiteral(_a0);
    }
    public bool is_BoolLiteral { get { return this is Literal_BoolLiteral; } }
    public bool is_IntLiteral { get { return this is Literal_IntLiteral; } }
    public bool is_DecLiteral { get { return this is Literal_DecLiteral; } }
    public bool is_StringLiteral { get { return this is Literal_StringLiteral; } }
    public bool dtor_BoolLiteral_a0 {
      get {
        var d = this;
        return ((Literal_BoolLiteral)d)._a0;
      }
    }
    public BigInteger dtor_IntLiteral_a0 {
      get {
        var d = this;
        return ((Literal_IntLiteral)d)._a0;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_DecLiteral_a0 {
      get {
        var d = this;
        return ((Literal_DecLiteral)d)._a0;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_StringLiteral_a0 {
      get {
        var d = this;
        return ((Literal_StringLiteral)d)._a0;
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
    public readonly BigInteger _a0;
    public Literal_IntLiteral(BigInteger _a0) : base() {
      this._a0 = _a0;
    }
    public override _ILiteral DowncastClone() {
      if (this is _ILiteral dt) { return dt; }
      return new Literal_IntLiteral(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Literal_IntLiteral;
      return oth != null && this._a0 == oth._a0;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Literal.IntLiteral";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class Literal_DecLiteral : Literal {
    public readonly Dafny.ISequence<Dafny.Rune> _a0;
    public Literal_DecLiteral(Dafny.ISequence<Dafny.Rune> _a0) : base() {
      this._a0 = _a0;
    }
    public override _ILiteral DowncastClone() {
      if (this is _ILiteral dt) { return dt; }
      return new Literal_DecLiteral(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Literal_DecLiteral;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Literal.DecLiteral";
      s += "(";
      s += this._a0.ToVerbatimString(true);
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
    public static Dafny.ISequence<Dafny.Rune> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISequence<Dafny.Rune> _13_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _14_traitBodies;
      Dafny.ISequence<Dafny.Rune> _out6;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _out7;
      DCOMP.COMP.GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(path, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(path)), Dafny.Set<DAST._IType>.FromElements(), out _out6, out _out7);
      _13_implBody = _out6;
      _14_traitBodies = _out7;
      _13_implBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub fn new() -> Self {\n"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}\n}\n")), _13_implBody);
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub struct r#"), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _13_implBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
      if ((new BigInteger(((c).dtor_superClasses).Count)).Sign == 1) {
        BigInteger _15_i;
        _15_i = BigInteger.Zero;
        while ((_15_i) < (new BigInteger(((c).dtor_superClasses).Count))) {
          DAST._IType _16_superClass;
          _16_superClass = ((c).dtor_superClasses).Select(_15_i);
          DAST._IType _source1 = _16_superClass;
          if (_source1.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _17___mcc_h0 = _source1.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _18___mcc_h1 = _source1.dtor_typeArgs;
            DAST._IResolvedType _19___mcc_h2 = _source1.dtor_resolved;
            DAST._IResolvedType _source2 = _19___mcc_h2;
            if (_source2.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _20___mcc_h6 = _source2.dtor_path;
            } else if (_source2.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _21___mcc_h8 = _source2.dtor_path;
              Dafny.ISequence<DAST._IType> _22_typeArgs = _18___mcc_h1;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _23_traitPath = _17___mcc_h0;
              {
                Dafny.ISequence<Dafny.Rune> _24_pathStr;
                Dafny.ISequence<Dafny.Rune> _out8;
                _out8 = DCOMP.COMP.GenPath(_23_traitPath);
                _24_pathStr = _out8;
                Dafny.ISequence<Dafny.Rune> _25_typeArgs;
                Dafny.ISequence<Dafny.Rune> _out9;
                _out9 = DCOMP.COMP.GenTypeArgs(_22_typeArgs, false);
                _25_typeArgs = _out9;
                Dafny.ISequence<Dafny.Rune> _26_body;
                _26_body = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                if ((_14_traitBodies).Contains(_23_traitPath)) {
                  _26_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Select(_14_traitBodies, _23_traitPath);
                }
                Dafny.ISequence<Dafny.Rune> _27_genSelfPath;
                Dafny.ISequence<Dafny.Rune> _out10;
                _out10 = DCOMP.COMP.GenPath(path);
                _27_genSelfPath = _out10;
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nimpl ")), _24_pathStr), _25_typeArgs), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" for ::std::rc::Rc<")), _27_genSelfPath), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("> {\n")), _26_body), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
              }
            } else {
            }
          } else if (_source1.is_Tuple) {
            Dafny.ISequence<DAST._IType> _28___mcc_h10 = _source1.dtor_Tuple_a0;
          } else if (_source1.is_Primitive) {
            DAST._IPrimitive _29___mcc_h12 = _source1.dtor_Primitive_a0;
          } else if (_source1.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _30___mcc_h14 = _source1.dtor_Passthrough_a0;
          } else {
            Dafny.ISequence<Dafny.Rune> _31___mcc_h16 = _source1.dtor_TypeArg_a0;
          }
          _15_i = (_15_i) + (BigInteger.One);
        }
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _32_typeParamsSet;
      _32_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<Dafny.Rune> _33_typeParams;
      _33_typeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _34_tpI;
      _34_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        _33_typeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<");
        while ((_34_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._IType _35_tp;
          _35_tp = ((t).dtor_typeParams).Select(_34_tpI);
          _32_typeParamsSet = Dafny.Set<DAST._IType>.Union(_32_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_35_tp));
          Dafny.ISequence<Dafny.Rune> _36_genTp;
          Dafny.ISequence<Dafny.Rune> _out11;
          _out11 = DCOMP.COMP.GenType(_35_tp, false);
          _36_genTp = _out11;
          _33_typeParams = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_33_typeParams, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _36_genTp), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          _34_tpI = (_34_tpI) + (BigInteger.One);
        }
        _33_typeParams = Dafny.Sequence<Dafny.Rune>.Concat(_33_typeParams, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _37_fullPath;
      _37_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<Dafny.Rune> _38_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _39___v3;
      Dafny.ISequence<Dafny.Rune> _out12;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _out13;
      DCOMP.COMP.GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_37_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_37_fullPath)), _32_typeParamsSet, out _out12, out _out13);
      _38_implBody = _out12;
      _39___v3 = _out13;
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub trait r#"), (t).dtor_name), _33_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _38_implBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenNewtype(DAST._INewtype c) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISequence<Dafny.Rune> _40_underlyingType;
      Dafny.ISequence<Dafny.Rune> _out14;
      _out14 = DCOMP.COMP.GenType((c).dtor_base, false);
      _40_underlyingType = _out14;
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub type r#"), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" =")), _40_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenDatatype(DAST._IDatatype c) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _41_typeParamsSet;
      _41_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<Dafny.Rune> _42_typeParams;
      _42_typeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _43_tpI;
      _43_tpI = BigInteger.Zero;
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _42_typeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<");
        while ((_43_tpI) < (new BigInteger(((c).dtor_typeParams).Count))) {
          DAST._IType _44_tp;
          _44_tp = ((c).dtor_typeParams).Select(_43_tpI);
          _41_typeParamsSet = Dafny.Set<DAST._IType>.Union(_41_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_44_tp));
          Dafny.ISequence<Dafny.Rune> _45_genTp;
          Dafny.ISequence<Dafny.Rune> _out15;
          _out15 = DCOMP.COMP.GenType(_44_tp, false);
          _45_genTp = _out15;
          _42_typeParams = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_42_typeParams, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _45_genTp), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          _43_tpI = (_43_tpI) + (BigInteger.One);
        }
        _42_typeParams = Dafny.Sequence<Dafny.Rune>.Concat(_42_typeParams, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
      Dafny.ISequence<Dafny.Rune> _46_ctors;
      _46_ctors = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _47_i;
      _47_i = BigInteger.Zero;
      while ((_47_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _48_ctor;
        _48_ctor = ((c).dtor_ctors).Select(_47_i);
        Dafny.ISequence<Dafny.Rune> _49_ctorBody;
        _49_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), (_48_ctor).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
        BigInteger _50_j;
        _50_j = BigInteger.Zero;
        while ((_50_j) < (new BigInteger(((_48_ctor).dtor_args).Count))) {
          DAST._IFormal _51_formal;
          _51_formal = ((_48_ctor).dtor_args).Select(_50_j);
          Dafny.ISequence<Dafny.Rune> _52_formalType;
          Dafny.ISequence<Dafny.Rune> _out16;
          _out16 = DCOMP.COMP.GenType((_51_formal).dtor_typ, false);
          _52_formalType = _out16;
          if ((c).dtor_isCo) {
            _49_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_49_ctorBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_51_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::LazyFieldWrapper<")), _52_formalType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">, "));
          } else {
            _49_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_49_ctorBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_51_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _52_formalType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          _50_j = (_50_j) + (BigInteger.One);
        }
        _49_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(_49_ctorBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        _46_ctors = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_46_ctors, _49_ctorBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"));
        _47_i = (_47_i) + (BigInteger.One);
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _53_selfPath;
      _53_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<Dafny.Rune> _54_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _55_traitBodies;
      Dafny.ISequence<Dafny.Rune> _out17;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _out18;
      DCOMP.COMP.GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(_53_selfPath)), _41_typeParamsSet, out _out17, out _out18);
      _54_implBody = _out17;
      _55_traitBodies = _out18;
      _47_i = BigInteger.Zero;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _56_emittedFields;
      _56_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      while ((_47_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _57_ctor;
        _57_ctor = ((c).dtor_ctors).Select(_47_i);
        BigInteger _58_j;
        _58_j = BigInteger.Zero;
        while ((_58_j) < (new BigInteger(((_57_ctor).dtor_args).Count))) {
          DAST._IFormal _59_formal;
          _59_formal = ((_57_ctor).dtor_args).Select(_58_j);
          if (!((_56_emittedFields).Contains((_59_formal).dtor_name))) {
            _56_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_56_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_59_formal).dtor_name));
            Dafny.ISequence<Dafny.Rune> _60_formalType;
            Dafny.ISequence<Dafny.Rune> _out19;
            _out19 = DCOMP.COMP.GenType((_59_formal).dtor_typ, false);
            _60_formalType = _out19;
            Dafny.ISequence<Dafny.Rune> _61_methodBody;
            _61_methodBody = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match self {\n");
            BigInteger _62_k;
            _62_k = BigInteger.Zero;
            while ((_62_k) < (new BigInteger(((c).dtor_ctors).Count))) {
              DAST._IDatatypeCtor _63_ctor2;
              _63_ctor2 = ((c).dtor_ctors).Select(_62_k);
              Dafny.ISequence<Dafny.Rune> _64_ctorMatch;
              _64_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_63_ctor2).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
              BigInteger _65_l;
              _65_l = BigInteger.Zero;
              bool _66_hasMatchingField;
              _66_hasMatchingField = false;
              while ((_65_l) < (new BigInteger(((_63_ctor2).dtor_args).Count))) {
                DAST._IFormal _67_formal2;
                _67_formal2 = ((_63_ctor2).dtor_args).Select(_65_l);
                if (((_59_formal).dtor_name).Equals((_67_formal2).dtor_name)) {
                  _66_hasMatchingField = true;
                }
                _64_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_64_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_67_formal2).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                _65_l = (_65_l) + (BigInteger.One);
              }
              if (_66_hasMatchingField) {
                if ((c).dtor_isCo) {
                  _64_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_64_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("} => ::std::ops::Deref::deref(&")), (_59_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0),\n"));
                } else {
                  _64_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_64_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("} => ")), (_59_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"));
                }
              } else {
                _64_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(_64_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("} => panic!(\"field does not exist on this variant\"),\n"));
              }
              _61_methodBody = Dafny.Sequence<Dafny.Rune>.Concat(_61_methodBody, _64_ctorMatch);
              _62_k = (_62_k) + (BigInteger.One);
            }
            _61_methodBody = Dafny.Sequence<Dafny.Rune>.Concat(_61_methodBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            _54_implBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_54_implBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub fn r#")), (_59_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(&self) -> &")), _60_formalType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _61_methodBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
          }
          _58_j = (_58_j) + (BigInteger.One);
        }
        _47_i = (_47_i) + (BigInteger.One);
      }
      Dafny.ISequence<Dafny.Rune> _68_constrainedTypeParams;
      _68_constrainedTypeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _43_tpI = BigInteger.Zero;
        _68_constrainedTypeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<");
        while ((_43_tpI) < (new BigInteger(((c).dtor_typeParams).Count))) {
          if ((_43_tpI).Sign == 1) {
            _68_constrainedTypeParams = Dafny.Sequence<Dafny.Rune>.Concat(_68_constrainedTypeParams, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          DAST._IType _69_tp;
          _69_tp = ((c).dtor_typeParams).Select(_43_tpI);
          Dafny.ISequence<Dafny.Rune> _70_genTp;
          Dafny.ISequence<Dafny.Rune> _out20;
          _out20 = DCOMP.COMP.GenType(_69_tp, false);
          _70_genTp = _out20;
          _68_constrainedTypeParams = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_68_constrainedTypeParams, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _70_genTp), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": Clone + ::std::cmp::PartialEq + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static"));
          _43_tpI = (_43_tpI) + (BigInteger.One);
        }
        _68_constrainedTypeParams = Dafny.Sequence<Dafny.Rune>.Concat(_68_constrainedTypeParams, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
      Dafny.ISequence<Dafny.Rune> _71_enumBody;
      _71_enumBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq)]\npub enum r#"), (c).dtor_name), _42_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _46_ctors), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _68_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" r#")), (c).dtor_name), _42_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _54_implBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
      Dafny.ISequence<Dafny.Rune> _72_printImpl;
      _72_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _68_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyPrint for r#")), (c).dtor_name), _42_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn fmt_print(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match self {\n"));
      _47_i = BigInteger.Zero;
      while ((_47_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _73_ctor;
        _73_ctor = ((c).dtor_ctors).Select(_47_i);
        Dafny.ISequence<Dafny.Rune> _74_ctorMatch;
        _74_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), (_73_ctor).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
        Dafny.ISequence<Dafny.Rune> _75_modulePrefix;
        _75_modulePrefix = (((((c).dtor_enclosingModule)).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(((c).dtor_enclosingModule), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _76_printRhs;
        _76_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(f, \""), _75_modulePrefix), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), (_73_ctor).dtor_name), (((_73_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?;")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?;"))));
        BigInteger _77_j;
        _77_j = BigInteger.Zero;
        while ((_77_j) < (new BigInteger(((_73_ctor).dtor_args).Count))) {
          DAST._IFormal _78_formal;
          _78_formal = ((_73_ctor).dtor_args).Select(_77_j);
          _74_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_74_ctorMatch, (_78_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_77_j).Sign == 1) {
            _76_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(_76_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nwrite!(f, \", \")?;"));
          }
          _76_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_76_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n::dafny_runtime::DafnyPrint::fmt_print(")), (_78_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", f)?;"));
          _77_j = (_77_j) + (BigInteger.One);
        }
        _74_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(_74_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        if ((_73_ctor).dtor_hasAnyArgs) {
          _76_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(_76_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nwrite!(f, \")\")?;"));
        }
        _76_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(_76_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nOk(())"));
        _72_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_72_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _74_ctorMatch), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" => {\n")), _76_printRhs), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}\n"));
        _47_i = (_47_i) + (BigInteger.One);
      }
      _72_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(_72_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n}\n}\n"));
      Dafny.ISequence<Dafny.Rune> _79_defaultImpl;
      _79_defaultImpl = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        _79_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _68_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::std::default::Default for r#")), (c).dtor_name), _42_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn default() -> Self {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), (((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
        _47_i = BigInteger.Zero;
        while ((_47_i) < (new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count))) {
          DAST._IFormal _80_formal;
          _80_formal = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_47_i);
          _79_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_79_defaultImpl, (_80_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": std::default::Default::default(),\n"));
          _47_i = (_47_i) + (BigInteger.One);
        }
        _79_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(_79_defaultImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n}\n}\n"));
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_71_enumBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _72_printImpl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _79_defaultImpl);
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenPath(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      if ((new BigInteger((p).Count)).Sign == 0) {
        s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Self");
        return s;
      } else {
        s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super::");
        BigInteger _81_i;
        _81_i = BigInteger.Zero;
        while ((_81_i) < (new BigInteger((p).Count))) {
          if ((_81_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), ((p).Select(_81_i)));
          _81_i = (_81_i) + (BigInteger.One);
        }
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      if ((new BigInteger((args).Count)).Sign == 1) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"));
        BigInteger _82_i;
        _82_i = BigInteger.Zero;
        while ((_82_i) < (new BigInteger((args).Count))) {
          if ((_82_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          Dafny.ISequence<Dafny.Rune> _83_genTp;
          Dafny.ISequence<Dafny.Rune> _out21;
          _out21 = DCOMP.COMP.GenType((args).Select(_82_i), inBinding);
          _83_genTp = _out21;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, _83_genTp);
          _82_i = (_82_i) + (BigInteger.One);
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenType(DAST._IType c, bool inBinding) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      DAST._IType _source3 = c;
      if (_source3.is_Path) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _84___mcc_h0 = _source3.dtor_Path_a0;
        Dafny.ISequence<DAST._IType> _85___mcc_h1 = _source3.dtor_typeArgs;
        DAST._IResolvedType _86___mcc_h2 = _source3.dtor_resolved;
        DAST._IResolvedType _87_resolved = _86___mcc_h2;
        Dafny.ISequence<DAST._IType> _88_args = _85___mcc_h1;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _89_p = _84___mcc_h0;
        {
          Dafny.ISequence<Dafny.Rune> _out22;
          _out22 = DCOMP.COMP.GenPath(_89_p);
          s = _out22;
          Dafny.ISequence<Dafny.Rune> _90_typeArgs;
          Dafny.ISequence<Dafny.Rune> _out23;
          _out23 = DCOMP.COMP.GenTypeArgs(_88_args, inBinding);
          _90_typeArgs = _out23;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, _90_typeArgs);
          DAST._IResolvedType _source4 = _87_resolved;
          if (_source4.is_Datatype) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _91___mcc_h8 = _source4.dtor_path;
            {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc<"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            }
          } else if (_source4.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _92___mcc_h10 = _source4.dtor_path;
            {
              if (inBinding) {
                s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_");
              } else {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              }
            }
          } else {
            DAST._IResolvedType _93_Primitive = _87_resolved;
          }
        }
      } else if (_source3.is_Tuple) {
        Dafny.ISequence<DAST._IType> _94___mcc_h3 = _source3.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IType> _95_types = _94___mcc_h3;
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
          BigInteger _96_i;
          _96_i = BigInteger.Zero;
          while ((_96_i) < (new BigInteger((_95_types).Count))) {
            if ((_96_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
            }
            Dafny.ISequence<Dafny.Rune> _97_generated;
            Dafny.ISequence<Dafny.Rune> _out24;
            _out24 = DCOMP.COMP.GenType((_95_types).Select(_96_i), inBinding);
            _97_generated = _out24;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _97_generated), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
            _96_i = (_96_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        }
      } else if (_source3.is_Primitive) {
        DAST._IPrimitive _98___mcc_h4 = _source3.dtor_Primitive_a0;
        DAST._IPrimitive _99_p = _98___mcc_h4;
        {
          DAST._IPrimitive _source5 = _99_p;
          if (_source5.is_String) {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("String");
          } else if (_source5.is_Bool) {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool");
          } else {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char");
          }
        }
      } else if (_source3.is_Passthrough) {
        Dafny.ISequence<Dafny.Rune> _100___mcc_h5 = _source3.dtor_Passthrough_a0;
        Dafny.ISequence<Dafny.Rune> _101_v = _100___mcc_h5;
        s = _101_v;
      } else {
        Dafny.ISequence<Dafny.Rune> _102___mcc_h6 = _source3.dtor_TypeArg_a0;
        Dafny.ISequence<Dafny.Rune> _source6 = _102___mcc_h6;
        Dafny.ISequence<Dafny.Rune> _103___mcc_h7 = _source6;
        Dafny.ISequence<Dafny.Rune> _104_name = _103___mcc_h7;
        s = _104_name;
      }
      return s;
    }
    public static void GenClassImplBody(Dafny.ISequence<DAST._IClassItem> body, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams, out Dafny.ISequence<Dafny.Rune> s, out Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> traitBodies) {
      s = Dafny.Sequence<Dafny.Rune>.Empty;
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _105_i;
      _105_i = BigInteger.Zero;
      while ((_105_i) < (new BigInteger((body).Count))) {
        DAST._IClassItem _source7 = (body).Select(_105_i);
        if (_source7.is_Method) {
          DAST._IMethod _106___mcc_h0 = _source7.dtor_Method_a0;
          DAST._IMethod _107_m = _106___mcc_h0;
          {
            DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source8 = (_107_m).dtor_overridingPath;
            if (_source8.is_Some) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _108___mcc_h2 = _source8.dtor_Some_a0;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _109_p = _108___mcc_h2;
              {
                Dafny.ISequence<Dafny.Rune> _110_existing;
                _110_existing = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                if ((traitBodies).Contains(_109_p)) {
                  _110_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Select(traitBodies, _109_p);
                }
                if ((new BigInteger((_110_existing).Count)).Sign == 1) {
                  _110_existing = Dafny.Sequence<Dafny.Rune>.Concat(_110_existing, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
                }
                Dafny.ISequence<Dafny.Rune> _111_genMethod;
                Dafny.ISequence<Dafny.Rune> _out25;
                _out25 = DCOMP.COMP.GenMethod(_107_m, true, enclosingType, enclosingTypeParams);
                _111_genMethod = _out25;
                _110_existing = Dafny.Sequence<Dafny.Rune>.Concat(_110_existing, _111_genMethod);
                traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>(_109_p, _110_existing)));
              }
            } else {
              {
                Dafny.ISequence<Dafny.Rune> _112_generated;
                Dafny.ISequence<Dafny.Rune> _out26;
                _out26 = DCOMP.COMP.GenMethod(_107_m, forTrait, enclosingType, enclosingTypeParams);
                _112_generated = _out26;
                s = Dafny.Sequence<Dafny.Rune>.Concat(s, _112_generated);
              }
            }
          }
        } else {
          DAST._IFormal _113___mcc_h1 = _source7.dtor_Field_a0;
          DAST._IFormal _114_f = _113___mcc_h1;
        }
        if ((new BigInteger((s).Count)).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        _105_i = (_105_i) + (BigInteger.One);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> GenParams(Dafny.ISequence<DAST._IFormal> @params) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _115_i;
      _115_i = BigInteger.Zero;
      while ((_115_i) < (new BigInteger((@params).Count))) {
        DAST._IFormal _116_param;
        _116_param = (@params).Select(_115_i);
        Dafny.ISequence<Dafny.Rune> _117_paramType;
        Dafny.ISequence<Dafny.Rune> _out27;
        _out27 = DCOMP.COMP.GenType((_116_param).dtor_typ, false);
        _117_paramType = _out27;
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_116_param).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": &")), _117_paramType);
        if ((_115_i) < ((new BigInteger((@params).Count)) - (BigInteger.One))) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
        }
        _115_i = (_115_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISequence<Dafny.Rune> _118_params;
      Dafny.ISequence<Dafny.Rune> _out28;
      _out28 = DCOMP.COMP.GenParams((m).dtor_params);
      _118_params = _out28;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _119_paramNames;
      _119_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _120_paramI;
      _120_paramI = BigInteger.Zero;
      while ((_120_paramI) < (new BigInteger(((m).dtor_params).Count))) {
        _119_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_119_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((((m).dtor_params).Select(_120_paramI)).dtor_name));
        _120_paramI = (_120_paramI) + (BigInteger.One);
      }
      if (!((m).dtor_isStatic)) {
        if (forTrait) {
          _118_params = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _118_params);
        } else {
          Dafny.ISequence<Dafny.Rune> _121_enclosingTypeString;
          Dafny.ISequence<Dafny.Rune> _out29;
          _out29 = DCOMP.COMP.GenType(enclosingType, false);
          _121_enclosingTypeString = _out29;
          _118_params = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self: &"), _121_enclosingTypeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _118_params);
        }
      }
      Dafny.ISequence<Dafny.Rune> _122_retType;
      _122_retType = (((new BigInteger(((m).dtor_outTypes).Count)) != (BigInteger.One)) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
      BigInteger _123_typeI;
      _123_typeI = BigInteger.Zero;
      while ((_123_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        if ((_123_typeI).Sign == 1) {
          _122_retType = Dafny.Sequence<Dafny.Rune>.Concat(_122_retType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
        }
        Dafny.ISequence<Dafny.Rune> _124_typeString;
        Dafny.ISequence<Dafny.Rune> _out30;
        _out30 = DCOMP.COMP.GenType(((m).dtor_outTypes).Select(_123_typeI), false);
        _124_typeString = _out30;
        _122_retType = Dafny.Sequence<Dafny.Rune>.Concat(_122_retType, _124_typeString);
        _123_typeI = (_123_typeI) + (BigInteger.One);
      }
      if ((new BigInteger(((m).dtor_outTypes).Count)) != (BigInteger.One)) {
        _122_retType = Dafny.Sequence<Dafny.Rune>.Concat(_122_retType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      }
      if (forTrait) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn r#"), (m).dtor_name);
      } else {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub fn r#"), (m).dtor_name);
      }
      Dafny.ISequence<DAST._IType> _125_typeParamsFiltered;
      _125_typeParamsFiltered = Dafny.Sequence<DAST._IType>.FromElements();
      BigInteger _126_typeParamI;
      _126_typeParamI = BigInteger.Zero;
      while ((_126_typeParamI) < (new BigInteger(((m).dtor_typeParams).Count))) {
        DAST._IType _127_typeParam;
        _127_typeParam = ((m).dtor_typeParams).Select(_126_typeParamI);
        if (!((enclosingTypeParams).Contains(_127_typeParam))) {
          _125_typeParamsFiltered = Dafny.Sequence<DAST._IType>.Concat(_125_typeParamsFiltered, Dafny.Sequence<DAST._IType>.FromElements(_127_typeParam));
        }
        _126_typeParamI = (_126_typeParamI) + (BigInteger.One);
      }
      if ((new BigInteger((_125_typeParamsFiltered).Count)).Sign == 1) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"));
        BigInteger _128_i;
        _128_i = BigInteger.Zero;
        while ((_128_i) < (new BigInteger((_125_typeParamsFiltered).Count))) {
          if ((_128_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          Dafny.ISequence<Dafny.Rune> _129_typeString;
          Dafny.ISequence<Dafny.Rune> _out31;
          _out31 = DCOMP.COMP.GenType((_125_typeParamsFiltered).Select(_128_i), false);
          _129_typeString = _out31;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _129_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": Clone + ::std::cmp::PartialEq + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static"));
          _128_i = (_128_i) + (BigInteger.One);
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _118_params), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), _122_retType);
      if ((m).dtor_hasBody) {
        Dafny.ISequence<Dafny.Rune> _130_earlyReturn;
        _130_earlyReturn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return;");
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source9 = (m).dtor_outVars;
        if (_source9.is_Some) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _131___mcc_h0 = _source9.dtor_Some_a0;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _132_outVars = _131___mcc_h0;
          {
            _130_earlyReturn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return (");
            BigInteger _133_outI;
            _133_outI = BigInteger.Zero;
            while ((_133_outI) < (new BigInteger((_132_outVars).Count))) {
              if ((_133_outI).Sign == 1) {
                _130_earlyReturn = Dafny.Sequence<Dafny.Rune>.Concat(_130_earlyReturn, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _134_outVar;
              _134_outVar = (_132_outVars).Select(_133_outI);
              _130_earlyReturn = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_130_earlyReturn, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_134_outVar));
              _133_outI = (_133_outI) + (BigInteger.One);
            }
            _130_earlyReturn = Dafny.Sequence<Dafny.Rune>.Concat(_130_earlyReturn, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");"));
          }
        } else {
        }
        Dafny.ISequence<Dafny.Rune> _135_body;
        Dafny.ISequence<Dafny.Rune> _out32;
        _out32 = DCOMP.COMP.GenStmts((m).dtor_body, _119_paramNames, _130_earlyReturn);
        _135_body = _out32;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source10 = (m).dtor_outVars;
        if (_source10.is_Some) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _136___mcc_h1 = _source10.dtor_Some_a0;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _137_outVars = _136___mcc_h1;
          {
            _135_body = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_135_body, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _130_earlyReturn);
          }
        } else {
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _135_body), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}\n"));
      } else {
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, Dafny.ISequence<Dafny.Rune> earlyReturn) {
      Dafny.ISequence<Dafny.Rune> generated = Dafny.Sequence<Dafny.Rune>.Empty;
      generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _138_i;
      _138_i = BigInteger.Zero;
      while ((_138_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _139_stmt;
        _139_stmt = (stmts).Select(_138_i);
        Dafny.ISequence<Dafny.Rune> _140_stmtString;
        Dafny.ISequence<Dafny.Rune> _out33;
        _out33 = DCOMP.COMP.GenStmt(_139_stmt, @params, earlyReturn);
        _140_stmtString = _out33;
        if ((_138_i).Sign == 1) {
          generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, _140_stmtString);
        _138_i = (_138_i) + (BigInteger.One);
      }
      return generated;
    }
    public static Dafny.ISequence<Dafny.Rune> GenStmt(DAST._IStatement stmt, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, Dafny.ISequence<Dafny.Rune> earlyReturn) {
      Dafny.ISequence<Dafny.Rune> generated = Dafny.Sequence<Dafny.Rune>.Empty;
      DAST._IStatement _source11 = stmt;
      if (_source11.is_DeclareVar) {
        Dafny.ISequence<Dafny.Rune> _141___mcc_h0 = _source11.dtor_name;
        DAST._IType _142___mcc_h1 = _source11.dtor_typ;
        DAST._IOptional<DAST._IExpression> _143___mcc_h2 = _source11.dtor_maybeValue;
        DAST._IOptional<DAST._IExpression> _source12 = _143___mcc_h2;
        if (_source12.is_Some) {
          DAST._IExpression _144___mcc_h3 = _source12.dtor_Some_a0;
          DAST._IExpression _145_expression = _144___mcc_h3;
          DAST._IType _146_typ = _142___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _147_name = _141___mcc_h0;
          {
            Dafny.ISequence<Dafny.Rune> _148_expr;
            bool _149___v6;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _150___v7;
            Dafny.ISequence<Dafny.Rune> _out34;
            bool _out35;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out36;
            DCOMP.COMP.GenExpr(_145_expression, @params, true, out _out34, out _out35, out _out36);
            _148_expr = _out34;
            _149___v6 = _out35;
            _150___v7 = _out36;
            Dafny.ISequence<Dafny.Rune> _151_typeString;
            Dafny.ISequence<Dafny.Rune> _out37;
            _out37 = DCOMP.COMP.GenType(_146_typ, true);
            _151_typeString = _out37;
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#"), _147_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _151_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _148_expr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          }
        } else {
          DAST._IType _152_typ = _142___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _153_name = _141___mcc_h0;
          {
            Dafny.ISequence<Dafny.Rune> _154_typeString;
            Dafny.ISequence<Dafny.Rune> _out38;
            _out38 = DCOMP.COMP.GenType(_152_typ, true);
            _154_typeString = _out38;
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#"), _153_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _154_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          }
        }
      } else if (_source11.is_Assign) {
        Dafny.ISequence<Dafny.Rune> _155___mcc_h4 = _source11.dtor_name;
        DAST._IExpression _156___mcc_h5 = _source11.dtor_value;
        DAST._IExpression _157_expression = _156___mcc_h5;
        Dafny.ISequence<Dafny.Rune> _158_name = _155___mcc_h4;
        {
          Dafny.ISequence<Dafny.Rune> _159_expr;
          bool _160___v8;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _161___v9;
          Dafny.ISequence<Dafny.Rune> _out39;
          bool _out40;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out41;
          DCOMP.COMP.GenExpr(_157_expression, @params, true, out _out39, out _out40, out _out41);
          _159_expr = _out39;
          _160___v8 = _out40;
          _161___v9 = _out41;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _158_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _159_expr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
        }
      } else if (_source11.is_If) {
        DAST._IExpression _162___mcc_h6 = _source11.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _163___mcc_h7 = _source11.dtor_thn;
        Dafny.ISequence<DAST._IStatement> _164___mcc_h8 = _source11.dtor_els;
        Dafny.ISequence<DAST._IStatement> _165_els = _164___mcc_h8;
        Dafny.ISequence<DAST._IStatement> _166_thn = _163___mcc_h7;
        DAST._IExpression _167_cond = _162___mcc_h6;
        {
          Dafny.ISequence<Dafny.Rune> _168_condString;
          bool _169___v10;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _170___v11;
          Dafny.ISequence<Dafny.Rune> _out42;
          bool _out43;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out44;
          DCOMP.COMP.GenExpr(_167_cond, @params, true, out _out42, out _out43, out _out44);
          _168_condString = _out42;
          _169___v10 = _out43;
          _170___v11 = _out44;
          Dafny.ISequence<Dafny.Rune> _171_thnString;
          Dafny.ISequence<Dafny.Rune> _out45;
          _out45 = DCOMP.COMP.GenStmts(_166_thn, @params, earlyReturn);
          _171_thnString = _out45;
          Dafny.ISequence<Dafny.Rune> _172_elsString;
          Dafny.ISequence<Dafny.Rune> _out46;
          _out46 = DCOMP.COMP.GenStmts(_165_els, @params, earlyReturn);
          _172_elsString = _out46;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if "), _168_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _171_thnString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _172_elsString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
        }
      } else if (_source11.is_While) {
        DAST._IExpression _173___mcc_h9 = _source11.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _174___mcc_h10 = _source11.dtor_body;
        Dafny.ISequence<DAST._IStatement> _175_body = _174___mcc_h10;
        DAST._IExpression _176_cond = _173___mcc_h9;
        {
          Dafny.ISequence<Dafny.Rune> _177_condString;
          bool _178___v12;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _179___v13;
          Dafny.ISequence<Dafny.Rune> _out47;
          bool _out48;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out49;
          DCOMP.COMP.GenExpr(_176_cond, @params, true, out _out47, out _out48, out _out49);
          _177_condString = _out47;
          _178___v12 = _out48;
          _179___v13 = _out49;
          Dafny.ISequence<Dafny.Rune> _180_bodyString;
          Dafny.ISequence<Dafny.Rune> _out50;
          _out50 = DCOMP.COMP.GenStmts(_175_body, @params, earlyReturn);
          _180_bodyString = _out50;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while "), _177_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _180_bodyString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
        }
      } else if (_source11.is_Call) {
        DAST._IExpression _181___mcc_h11 = _source11.dtor_on;
        Dafny.ISequence<Dafny.Rune> _182___mcc_h12 = _source11.dtor_name;
        Dafny.ISequence<DAST._IType> _183___mcc_h13 = _source11.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _184___mcc_h14 = _source11.dtor_args;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _185___mcc_h15 = _source11.dtor_outs;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _186_maybeOutVars = _185___mcc_h15;
        Dafny.ISequence<DAST._IExpression> _187_args = _184___mcc_h14;
        Dafny.ISequence<DAST._IType> _188_typeArgs = _183___mcc_h13;
        Dafny.ISequence<Dafny.Rune> _189_name = _182___mcc_h12;
        DAST._IExpression _190_on = _181___mcc_h11;
        {
          Dafny.ISequence<Dafny.Rune> _191_typeArgString;
          _191_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_188_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _192_typeI;
            _192_typeI = BigInteger.Zero;
            _191_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<");
            while ((_192_typeI) < (new BigInteger((_188_typeArgs).Count))) {
              if ((_192_typeI).Sign == 1) {
                _191_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_191_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _193_typeString;
              Dafny.ISequence<Dafny.Rune> _out51;
              _out51 = DCOMP.COMP.GenType((_188_typeArgs).Select(_192_typeI), false);
              _193_typeString = _out51;
              _191_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_191_typeArgString, _193_typeString);
              _192_typeI = (_192_typeI) + (BigInteger.One);
            }
            _191_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_191_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
          Dafny.ISequence<Dafny.Rune> _194_argString;
          _194_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _195_i;
          _195_i = BigInteger.Zero;
          while ((_195_i) < (new BigInteger((_187_args).Count))) {
            if ((_195_i).Sign == 1) {
              _194_argString = Dafny.Sequence<Dafny.Rune>.Concat(_194_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _196_argExpr;
            bool _197_isOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _198___v14;
            Dafny.ISequence<Dafny.Rune> _out52;
            bool _out53;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out54;
            DCOMP.COMP.GenExpr((_187_args).Select(_195_i), @params, false, out _out52, out _out53, out _out54);
            _196_argExpr = _out52;
            _197_isOwned = _out53;
            _198___v14 = _out54;
            _194_argString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_194_argString, ((_197_isOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _196_argExpr);
            _195_i = (_195_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _199_enclosingString;
          bool _200___v15;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _201___v16;
          Dafny.ISequence<Dafny.Rune> _out55;
          bool _out56;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out57;
          DCOMP.COMP.GenExpr(_190_on, @params, true, out _out55, out _out56, out _out57);
          _199_enclosingString = _out55;
          _200___v15 = _out56;
          _201___v16 = _out57;
          DAST._IExpression _source13 = _190_on;
          if (_source13.is_Literal) {
            DAST._ILiteral _202___mcc_h18 = _source13.dtor_Literal_a0;
            {
              _199_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _199_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source13.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _203___mcc_h20 = _source13.dtor_Ident_a0;
            {
              _199_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _199_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source13.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _204___mcc_h22 = _source13.dtor_Companion_a0;
            {
              _199_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(_199_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
            }
          } else if (_source13.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _205___mcc_h24 = _source13.dtor_Tuple_a0;
            {
              _199_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _199_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source13.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _206___mcc_h26 = _source13.dtor_path;
            Dafny.ISequence<DAST._IExpression> _207___mcc_h27 = _source13.dtor_args;
            {
              _199_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _199_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source13.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _208___mcc_h30 = _source13.dtor_path;
            Dafny.ISequence<Dafny.Rune> _209___mcc_h31 = _source13.dtor_variant;
            bool _210___mcc_h32 = _source13.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _211___mcc_h33 = _source13.dtor_contents;
            {
              _199_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _199_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source13.is_This) {
            {
              _199_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _199_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source13.is_Ite) {
            DAST._IExpression _212___mcc_h38 = _source13.dtor_cond;
            DAST._IExpression _213___mcc_h39 = _source13.dtor_thn;
            DAST._IExpression _214___mcc_h40 = _source13.dtor_els;
            {
              _199_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _199_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source13.is_UnOp) {
            DAST._IUnaryOp _215___mcc_h44 = _source13.dtor_unOp;
            DAST._IExpression _216___mcc_h45 = _source13.dtor_expr;
            {
              _199_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _199_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source13.is_BinOp) {
            Dafny.ISequence<Dafny.Rune> _217___mcc_h48 = _source13.dtor_op;
            DAST._IExpression _218___mcc_h49 = _source13.dtor_left;
            DAST._IExpression _219___mcc_h50 = _source13.dtor_right;
            {
              _199_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _199_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source13.is_Select) {
            DAST._IExpression _220___mcc_h54 = _source13.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _221___mcc_h55 = _source13.dtor_field;
            bool _222___mcc_h56 = _source13.dtor_onDatatype;
            {
              _199_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _199_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source13.is_TupleSelect) {
            DAST._IExpression _223___mcc_h60 = _source13.dtor_expr;
            BigInteger _224___mcc_h61 = _source13.dtor_index;
            {
              _199_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _199_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source13.is_Call) {
            DAST._IExpression _225___mcc_h64 = _source13.dtor_on;
            Dafny.ISequence<Dafny.Rune> _226___mcc_h65 = _source13.dtor_name;
            Dafny.ISequence<DAST._IType> _227___mcc_h66 = _source13.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _228___mcc_h67 = _source13.dtor_args;
            {
              _199_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _199_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source13.is_TypeTest) {
            DAST._IExpression _229___mcc_h72 = _source13.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _230___mcc_h73 = _source13.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _231___mcc_h74 = _source13.dtor_variant;
            {
              _199_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _199_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else {
            DAST._IType _232___mcc_h78 = _source13.dtor_typ;
            {
              _199_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _199_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          }
          Dafny.ISequence<Dafny.Rune> _233_receiver;
          _233_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source14 = _186_maybeOutVars;
          if (_source14.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _234___mcc_h80 = _source14.dtor_Some_a0;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _235_outVars = _234___mcc_h80;
            {
              if ((new BigInteger((_235_outVars).Count)) > (BigInteger.One)) {
                _233_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
              }
              BigInteger _236_outI;
              _236_outI = BigInteger.Zero;
              while ((_236_outI) < (new BigInteger((_235_outVars).Count))) {
                if ((_236_outI).Sign == 1) {
                  _233_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_233_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                Dafny.ISequence<Dafny.Rune> _237_outVar;
                _237_outVar = (_235_outVars).Select(_236_outI);
                _233_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_233_receiver, (_237_outVar));
                _236_outI = (_236_outI) + (BigInteger.One);
              }
              if ((new BigInteger((_235_outVars).Count)) > (BigInteger.One)) {
                _233_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_233_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
            }
          } else {
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((!(_233_receiver).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_233_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), _199_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _189_name), _191_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _194_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");"));
        }
      } else if (_source11.is_Return) {
        DAST._IExpression _238___mcc_h16 = _source11.dtor_expr;
        DAST._IExpression _239_expr = _238___mcc_h16;
        {
          Dafny.ISequence<Dafny.Rune> _240_exprString;
          bool _241___v19;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _242___v20;
          Dafny.ISequence<Dafny.Rune> _out58;
          bool _out59;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out60;
          DCOMP.COMP.GenExpr(_239_expr, @params, true, out _out58, out _out59, out _out60);
          _240_exprString = _out58;
          _241___v19 = _out59;
          _242___v20 = _out60;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return "), _240_exprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
        }
      } else if (_source11.is_EarlyReturn) {
        {
          generated = earlyReturn;
        }
      } else if (_source11.is_Halt) {
        {
          generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"Halt\");");
        }
      } else {
        DAST._IExpression _243___mcc_h17 = _source11.dtor_Print_a0;
        DAST._IExpression _244_e = _243___mcc_h17;
        {
          Dafny.ISequence<Dafny.Rune> _245_printedExpr;
          bool _246_isOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _247___v21;
          Dafny.ISequence<Dafny.Rune> _out61;
          bool _out62;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out63;
          DCOMP.COMP.GenExpr(_244_e, @params, false, out _out61, out _out62, out _out63);
          _245_printedExpr = _out61;
          _246_isOwned = _out62;
          _247___v21 = _out63;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper("), ((_246_isOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _245_printedExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("));"));
        }
      }
      return generated;
    }
    public static void GenExpr(DAST._IExpression e, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, bool mustOwn, out Dafny.ISequence<Dafny.Rune> s, out bool isOwned, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents) {
      s = Dafny.Sequence<Dafny.Rune>.Empty;
      isOwned = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source15 = e;
      if (_source15.is_Literal) {
        DAST._ILiteral _248___mcc_h0 = _source15.dtor_Literal_a0;
        DAST._ILiteral _source16 = _248___mcc_h0;
        if (_source16.is_BoolLiteral) {
          bool _249___mcc_h1 = _source16.dtor_BoolLiteral_a0;
          if ((_249___mcc_h1) == (false)) {
            {
              s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false");
              isOwned = true;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            }
          } else {
            {
              s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true");
              isOwned = true;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            }
          }
        } else if (_source16.is_IntLiteral) {
          BigInteger _250___mcc_h2 = _source16.dtor_IntLiteral_a0;
          BigInteger _251_i = _250___mcc_h2;
          {
            if ((_251_i).Sign == -1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-"), DCOMP.__default.natToString((BigInteger.Zero) - (_251_i)));
            } else {
              s = DCOMP.__default.natToString(_251_i);
            }
            isOwned = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source16.is_DecLiteral) {
          Dafny.ISequence<Dafny.Rune> _252___mcc_h3 = _source16.dtor_DecLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _253_l = _252___mcc_h3;
          {
            s = _253_l;
            isOwned = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else {
          Dafny.ISequence<Dafny.Rune> _254___mcc_h4 = _source16.dtor_StringLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _255_l = _254___mcc_h4;
          {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\""), _255_l), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\".to_string()"));
            isOwned = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        }
      } else if (_source15.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _256___mcc_h5 = _source15.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _257_name = _256___mcc_h5;
        {
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _257_name);
          if ((@params).Contains(_257_name)) {
            if (mustOwn) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
              isOwned = true;
            } else {
              isOwned = false;
            }
          } else {
            if (mustOwn) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
              isOwned = true;
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              isOwned = false;
            }
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_257_name);
        }
      } else if (_source15.is_Companion) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _258___mcc_h6 = _source15.dtor_Companion_a0;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _259_path = _258___mcc_h6;
        {
          Dafny.ISequence<Dafny.Rune> _out64;
          _out64 = DCOMP.COMP.GenPath(_259_path);
          s = _out64;
          isOwned = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source15.is_Tuple) {
        Dafny.ISequence<DAST._IExpression> _260___mcc_h7 = _source15.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IExpression> _261_values = _260___mcc_h7;
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _262_i;
          _262_i = BigInteger.Zero;
          while ((_262_i) < (new BigInteger((_261_values).Count))) {
            if ((_262_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
            }
            Dafny.ISequence<Dafny.Rune> _263_recursiveGen;
            bool _264___v22;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _265_recIdents;
            Dafny.ISequence<Dafny.Rune> _out65;
            bool _out66;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out67;
            DCOMP.COMP.GenExpr((_261_values).Select(_262_i), @params, true, out _out65, out _out66, out _out67);
            _263_recursiveGen = _out65;
            _264___v22 = _out66;
            _265_recIdents = _out67;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _263_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _265_recIdents);
            _262_i = (_262_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
        }
      } else if (_source15.is_New) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _266___mcc_h8 = _source15.dtor_path;
        Dafny.ISequence<DAST._IExpression> _267___mcc_h9 = _source15.dtor_args;
        Dafny.ISequence<DAST._IExpression> _268_args = _267___mcc_h9;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _269_path = _266___mcc_h8;
        {
          Dafny.ISequence<Dafny.Rune> _270_path;
          Dafny.ISequence<Dafny.Rune> _out68;
          _out68 = DCOMP.COMP.GenPath(_269_path);
          _270_path = _out68;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _270_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new("));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _271_i;
          _271_i = BigInteger.Zero;
          while ((_271_i) < (new BigInteger((_268_args).Count))) {
            if ((_271_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _272_recursiveGen;
            bool _273___v23;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _274_recIdents;
            Dafny.ISequence<Dafny.Rune> _out69;
            bool _out70;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out71;
            DCOMP.COMP.GenExpr((_268_args).Select(_271_i), @params, true, out _out69, out _out70, out _out71);
            _272_recursiveGen = _out69;
            _273___v23 = _out70;
            _274_recIdents = _out71;
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _272_recursiveGen);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _274_recIdents);
            _271_i = (_271_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
        }
      } else if (_source15.is_DatatypeValue) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _275___mcc_h10 = _source15.dtor_path;
        Dafny.ISequence<Dafny.Rune> _276___mcc_h11 = _source15.dtor_variant;
        bool _277___mcc_h12 = _source15.dtor_isCo;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _278___mcc_h13 = _source15.dtor_contents;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _279_values = _278___mcc_h13;
        bool _280_isCo = _277___mcc_h12;
        Dafny.ISequence<Dafny.Rune> _281_variant = _276___mcc_h11;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _282_path = _275___mcc_h10;
        {
          Dafny.ISequence<Dafny.Rune> _283_path;
          Dafny.ISequence<Dafny.Rune> _out72;
          _out72 = DCOMP.COMP.GenPath(_282_path);
          _283_path = _out72;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _283_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _281_variant);
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _284_i;
          _284_i = BigInteger.Zero;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {"));
          while ((_284_i) < (new BigInteger((_279_values).Count))) {
            _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs0 = (_279_values).Select(_284_i);
            Dafny.ISequence<Dafny.Rune> _285_name = _let_tmp_rhs0.dtor__0;
            DAST._IExpression _286_value = _let_tmp_rhs0.dtor__1;
            if ((_284_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            if (_280_isCo) {
              Dafny.ISequence<Dafny.Rune> _287_recursiveGen;
              bool _288___v24;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _289_recIdents;
              Dafny.ISequence<Dafny.Rune> _out73;
              bool _out74;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out75;
              DCOMP.COMP.GenExpr(_286_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), true, out _out73, out _out74, out _out75);
              _287_recursiveGen = _out73;
              _288___v24 = _out74;
              _289_recIdents = _out75;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _289_recIdents);
              Dafny.ISequence<Dafny.Rune> _290_allReadCloned;
              _290_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              while (!(_289_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                Dafny.ISequence<Dafny.Rune> _291_next;
                foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_0 in (_289_recIdents).Elements) {
                  _291_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_0;
                  if ((_289_recIdents).Contains(_291_next)) {
                    goto after__ASSIGN_SUCH_THAT_0;
                  }
                }
                throw new System.Exception("assign-such-that search produced no value (line 765)");
              after__ASSIGN_SUCH_THAT_0:;
                _290_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_290_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), _291_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _291_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                _289_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_289_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_291_next));
              }
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _285_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(Box::new({\n")), _290_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), _287_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
            } else {
              Dafny.ISequence<Dafny.Rune> _292_recursiveGen;
              bool _293___v25;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _294_recIdents;
              Dafny.ISequence<Dafny.Rune> _out76;
              bool _out77;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out78;
              DCOMP.COMP.GenExpr(_286_value, @params, true, out _out76, out _out77, out _out78);
              _292_recursiveGen = _out76;
              _293___v25 = _out77;
              _294_recIdents = _out78;
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _285_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _292_recursiveGen);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _294_recIdents);
            }
            _284_i = (_284_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" })"));
          isOwned = true;
        }
      } else if (_source15.is_This) {
        {
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self.clone()");
            isOwned = true;
          } else {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
            isOwned = false;
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"));
        }
      } else if (_source15.is_Ite) {
        DAST._IExpression _295___mcc_h14 = _source15.dtor_cond;
        DAST._IExpression _296___mcc_h15 = _source15.dtor_thn;
        DAST._IExpression _297___mcc_h16 = _source15.dtor_els;
        DAST._IExpression _298_f = _297___mcc_h16;
        DAST._IExpression _299_t = _296___mcc_h15;
        DAST._IExpression _300_cond = _295___mcc_h14;
        {
          Dafny.ISequence<Dafny.Rune> _301_condString;
          bool _302___v26;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _303_recIdentsCond;
          Dafny.ISequence<Dafny.Rune> _out79;
          bool _out80;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out81;
          DCOMP.COMP.GenExpr(_300_cond, @params, true, out _out79, out _out80, out _out81);
          _301_condString = _out79;
          _302___v26 = _out80;
          _303_recIdentsCond = _out81;
          Dafny.ISequence<Dafny.Rune> _304___v27;
          bool _305_tHasToBeOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _306___v28;
          Dafny.ISequence<Dafny.Rune> _out82;
          bool _out83;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out84;
          DCOMP.COMP.GenExpr(_299_t, @params, mustOwn, out _out82, out _out83, out _out84);
          _304___v27 = _out82;
          _305_tHasToBeOwned = _out83;
          _306___v28 = _out84;
          Dafny.ISequence<Dafny.Rune> _307_fString;
          bool _308_fOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _309_recIdentsF;
          Dafny.ISequence<Dafny.Rune> _out85;
          bool _out86;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out87;
          DCOMP.COMP.GenExpr(_298_f, @params, _305_tHasToBeOwned, out _out85, out _out86, out _out87);
          _307_fString = _out85;
          _308_fOwned = _out86;
          _309_recIdentsF = _out87;
          Dafny.ISequence<Dafny.Rune> _310_tString;
          bool _311___v29;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _312_recIdentsT;
          Dafny.ISequence<Dafny.Rune> _out88;
          bool _out89;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out90;
          DCOMP.COMP.GenExpr(_299_t, @params, _308_fOwned, out _out88, out _out89, out _out90);
          _310_tString = _out88;
          _311___v29 = _out89;
          _312_recIdentsT = _out90;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _301_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _310_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _307_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})"));
          isOwned = _308_fOwned;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_303_recIdentsCond, _312_recIdentsT), _309_recIdentsF);
        }
      } else if (_source15.is_UnOp) {
        DAST._IUnaryOp _313___mcc_h17 = _source15.dtor_unOp;
        DAST._IExpression _314___mcc_h18 = _source15.dtor_expr;
        DAST._IUnaryOp _source17 = _313___mcc_h17;
        if (_source17.is_Not) {
          DAST._IExpression _315_e = _314___mcc_h18;
          {
            Dafny.ISequence<Dafny.Rune> _316_recursiveGen;
            bool _317___v30;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _318_recIdents;
            Dafny.ISequence<Dafny.Rune> _out91;
            bool _out92;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out93;
            DCOMP.COMP.GenExpr(_315_e, @params, true, out _out91, out _out92, out _out93);
            _316_recursiveGen = _out91;
            _317___v30 = _out92;
            _318_recIdents = _out93;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!("), _316_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _318_recIdents;
          }
        } else if (_source17.is_BitwiseNot) {
          DAST._IExpression _319_e = _314___mcc_h18;
          {
            Dafny.ISequence<Dafny.Rune> _320_recursiveGen;
            bool _321___v31;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _322_recIdents;
            Dafny.ISequence<Dafny.Rune> _out94;
            bool _out95;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out96;
            DCOMP.COMP.GenExpr(_319_e, @params, true, out _out94, out _out95, out _out96);
            _320_recursiveGen = _out94;
            _321___v31 = _out95;
            _322_recIdents = _out96;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~("), _320_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _322_recIdents;
          }
        } else {
          DAST._IExpression _323_e = _314___mcc_h18;
          {
            Dafny.ISequence<Dafny.Rune> _324_recursiveGen;
            bool _325___v32;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _326_recIdents;
            Dafny.ISequence<Dafny.Rune> _out97;
            bool _out98;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out99;
            DCOMP.COMP.GenExpr(_323_e, @params, false, out _out97, out _out98, out _out99);
            _324_recursiveGen = _out97;
            _325___v32 = _out98;
            _326_recIdents = _out99;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _324_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").len()"));
            isOwned = true;
            readIdents = _326_recIdents;
          }
        }
      } else if (_source15.is_BinOp) {
        Dafny.ISequence<Dafny.Rune> _327___mcc_h19 = _source15.dtor_op;
        DAST._IExpression _328___mcc_h20 = _source15.dtor_left;
        DAST._IExpression _329___mcc_h21 = _source15.dtor_right;
        DAST._IExpression _330_r = _329___mcc_h21;
        DAST._IExpression _331_l = _328___mcc_h20;
        Dafny.ISequence<Dafny.Rune> _332_op = _327___mcc_h19;
        {
          Dafny.ISequence<Dafny.Rune> _333_left;
          bool _334___v33;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _335_recIdentsL;
          Dafny.ISequence<Dafny.Rune> _out100;
          bool _out101;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out102;
          DCOMP.COMP.GenExpr(_331_l, @params, true, out _out100, out _out101, out _out102);
          _333_left = _out100;
          _334___v33 = _out101;
          _335_recIdentsL = _out102;
          Dafny.ISequence<Dafny.Rune> _336_right;
          bool _337___v34;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _338_recIdentsR;
          Dafny.ISequence<Dafny.Rune> _out103;
          bool _out104;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out105;
          DCOMP.COMP.GenExpr(_330_r, @params, true, out _out103, out _out104, out _out105);
          _336_right = _out103;
          _337___v34 = _out104;
          _338_recIdentsR = _out105;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _332_op), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _336_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_335_recIdentsL, _338_recIdentsR);
        }
      } else if (_source15.is_Select) {
        DAST._IExpression _339___mcc_h22 = _source15.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _340___mcc_h23 = _source15.dtor_field;
        bool _341___mcc_h24 = _source15.dtor_onDatatype;
        bool _342_isDatatype = _341___mcc_h24;
        Dafny.ISequence<Dafny.Rune> _343_field = _340___mcc_h23;
        DAST._IExpression _344_on = _339___mcc_h22;
        {
          Dafny.ISequence<Dafny.Rune> _345_onString;
          bool _346___v35;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _347_recIdents;
          Dafny.ISequence<Dafny.Rune> _out106;
          bool _out107;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out108;
          DCOMP.COMP.GenExpr(_344_on, @params, false, out _out106, out _out107, out _out108);
          _345_onString = _out106;
          _346___v35 = _out107;
          _347_recIdents = _out108;
          if (_342_isDatatype) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _345_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _343_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
            if (mustOwn) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            } else {
              isOwned = false;
            }
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _345_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _343_field);
            if (mustOwn) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            } else {
              isOwned = false;
            }
          }
          readIdents = _347_recIdents;
        }
      } else if (_source15.is_TupleSelect) {
        DAST._IExpression _348___mcc_h25 = _source15.dtor_expr;
        BigInteger _349___mcc_h26 = _source15.dtor_index;
        BigInteger _350_idx = _349___mcc_h26;
        DAST._IExpression _351_on = _348___mcc_h25;
        {
          Dafny.ISequence<Dafny.Rune> _352_onString;
          bool _353___v36;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _354_recIdents;
          Dafny.ISequence<Dafny.Rune> _out109;
          bool _out110;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out111;
          DCOMP.COMP.GenExpr(_351_on, @params, false, out _out109, out _out110, out _out111);
          _352_onString = _out109;
          _353___v36 = _out110;
          _354_recIdents = _out111;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _352_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").")), DCOMP.__default.natToString(_350_idx));
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
            isOwned = true;
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
            isOwned = false;
          }
          readIdents = _354_recIdents;
        }
      } else if (_source15.is_Call) {
        DAST._IExpression _355___mcc_h27 = _source15.dtor_on;
        Dafny.ISequence<Dafny.Rune> _356___mcc_h28 = _source15.dtor_name;
        Dafny.ISequence<DAST._IType> _357___mcc_h29 = _source15.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _358___mcc_h30 = _source15.dtor_args;
        Dafny.ISequence<DAST._IExpression> _359_args = _358___mcc_h30;
        Dafny.ISequence<DAST._IType> _360_typeArgs = _357___mcc_h29;
        Dafny.ISequence<Dafny.Rune> _361_name = _356___mcc_h28;
        DAST._IExpression _362_on = _355___mcc_h27;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _363_typeArgString;
          _363_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_360_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _364_typeI;
            _364_typeI = BigInteger.Zero;
            _363_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<");
            while ((_364_typeI) < (new BigInteger((_360_typeArgs).Count))) {
              if ((_364_typeI).Sign == 1) {
                _363_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_363_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _365_typeString;
              Dafny.ISequence<Dafny.Rune> _out112;
              _out112 = DCOMP.COMP.GenType((_360_typeArgs).Select(_364_typeI), false);
              _365_typeString = _out112;
              _363_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_363_typeArgString, _365_typeString);
              _364_typeI = (_364_typeI) + (BigInteger.One);
            }
            _363_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_363_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
          Dafny.ISequence<Dafny.Rune> _366_argString;
          _366_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _367_i;
          _367_i = BigInteger.Zero;
          while ((_367_i) < (new BigInteger((_359_args).Count))) {
            if ((_367_i).Sign == 1) {
              _366_argString = Dafny.Sequence<Dafny.Rune>.Concat(_366_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _368_argExpr;
            bool _369_isOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _370_recIdents;
            Dafny.ISequence<Dafny.Rune> _out113;
            bool _out114;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out115;
            DCOMP.COMP.GenExpr((_359_args).Select(_367_i), @params, false, out _out113, out _out114, out _out115);
            _368_argExpr = _out113;
            _369_isOwned = _out114;
            _370_recIdents = _out115;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _370_recIdents);
            _366_argString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_366_argString, ((_369_isOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _368_argExpr);
            _367_i = (_367_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _371_enclosingString;
          bool _372___v37;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _373_recIdents;
          Dafny.ISequence<Dafny.Rune> _out116;
          bool _out117;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out118;
          DCOMP.COMP.GenExpr(_362_on, @params, false, out _out116, out _out117, out _out118);
          _371_enclosingString = _out116;
          _372___v37 = _out117;
          _373_recIdents = _out118;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _373_recIdents);
          DAST._IExpression _source18 = _362_on;
          if (_source18.is_Literal) {
            DAST._ILiteral _374___mcc_h35 = _source18.dtor_Literal_a0;
            {
              _371_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _371_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _375___mcc_h37 = _source18.dtor_Ident_a0;
            {
              _371_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _371_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _376___mcc_h39 = _source18.dtor_Companion_a0;
            {
              _371_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(_371_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
            }
          } else if (_source18.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _377___mcc_h41 = _source18.dtor_Tuple_a0;
            {
              _371_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _371_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _378___mcc_h43 = _source18.dtor_path;
            Dafny.ISequence<DAST._IExpression> _379___mcc_h44 = _source18.dtor_args;
            {
              _371_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _371_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _380___mcc_h47 = _source18.dtor_path;
            Dafny.ISequence<Dafny.Rune> _381___mcc_h48 = _source18.dtor_variant;
            bool _382___mcc_h49 = _source18.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _383___mcc_h50 = _source18.dtor_contents;
            {
              _371_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _371_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_This) {
            {
              _371_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _371_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Ite) {
            DAST._IExpression _384___mcc_h55 = _source18.dtor_cond;
            DAST._IExpression _385___mcc_h56 = _source18.dtor_thn;
            DAST._IExpression _386___mcc_h57 = _source18.dtor_els;
            {
              _371_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _371_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_UnOp) {
            DAST._IUnaryOp _387___mcc_h61 = _source18.dtor_unOp;
            DAST._IExpression _388___mcc_h62 = _source18.dtor_expr;
            {
              _371_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _371_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_BinOp) {
            Dafny.ISequence<Dafny.Rune> _389___mcc_h65 = _source18.dtor_op;
            DAST._IExpression _390___mcc_h66 = _source18.dtor_left;
            DAST._IExpression _391___mcc_h67 = _source18.dtor_right;
            {
              _371_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _371_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Select) {
            DAST._IExpression _392___mcc_h71 = _source18.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _393___mcc_h72 = _source18.dtor_field;
            bool _394___mcc_h73 = _source18.dtor_onDatatype;
            {
              _371_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _371_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_TupleSelect) {
            DAST._IExpression _395___mcc_h77 = _source18.dtor_expr;
            BigInteger _396___mcc_h78 = _source18.dtor_index;
            {
              _371_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _371_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Call) {
            DAST._IExpression _397___mcc_h81 = _source18.dtor_on;
            Dafny.ISequence<Dafny.Rune> _398___mcc_h82 = _source18.dtor_name;
            Dafny.ISequence<DAST._IType> _399___mcc_h83 = _source18.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _400___mcc_h84 = _source18.dtor_args;
            {
              _371_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _371_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_TypeTest) {
            DAST._IExpression _401___mcc_h89 = _source18.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _402___mcc_h90 = _source18.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _403___mcc_h91 = _source18.dtor_variant;
            {
              _371_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _371_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else {
            DAST._IType _404___mcc_h95 = _source18.dtor_typ;
            {
              _371_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _371_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_371_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _361_name), _363_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _366_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
        }
      } else if (_source15.is_TypeTest) {
        DAST._IExpression _405___mcc_h31 = _source15.dtor_on;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _406___mcc_h32 = _source15.dtor_dType;
        Dafny.ISequence<Dafny.Rune> _407___mcc_h33 = _source15.dtor_variant;
        Dafny.ISequence<Dafny.Rune> _408_variant = _407___mcc_h33;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _409_dType = _406___mcc_h32;
        DAST._IExpression _410_on = _405___mcc_h31;
        {
          Dafny.ISequence<Dafny.Rune> _411_exprGen;
          bool _412___v40;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _413_recIdents;
          Dafny.ISequence<Dafny.Rune> _out119;
          bool _out120;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out121;
          DCOMP.COMP.GenExpr(_410_on, @params, false, out _out119, out _out120, out _out121);
          _411_exprGen = _out119;
          _412___v40 = _out120;
          _413_recIdents = _out121;
          Dafny.ISequence<Dafny.Rune> _414_dTypePath;
          Dafny.ISequence<Dafny.Rune> _out122;
          _out122 = DCOMP.COMP.GenPath(_409_dType);
          _414_dTypePath = _out122;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!("), _411_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref(), ")), _414_dTypePath), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _408_variant), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. })"));
          isOwned = true;
          readIdents = _413_recIdents;
        }
      } else {
        DAST._IType _415___mcc_h34 = _source15.dtor_typ;
        DAST._IType _416_typ = _415___mcc_h34;
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::default::Default::default()");
          isOwned = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      }
    }
    public static Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern crate dafny_runtime;\n"));
      BigInteger _417_i;
      _417_i = BigInteger.Zero;
      while ((_417_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _418_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        Dafny.ISequence<Dafny.Rune> _out123;
        _out123 = DCOMP.COMP.GenModule((p).Select(_417_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _418_generated = _out123;
        if ((_417_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _418_generated);
        _417_i = (_417_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _419_i;
      _419_i = BigInteger.Zero;
      while ((_419_i) < (new BigInteger((fullName).Count))) {
        if ((_419_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (fullName).Select(_419_i));
        _419_i = (_419_i) + (BigInteger.One);
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("();\n}"));
      return s;
    }
  }
} // end of namespace DCOMP

