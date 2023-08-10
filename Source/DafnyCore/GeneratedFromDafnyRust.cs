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
    DAST._IOptional<DAST._IExpression> dtor_witnessExpr { get; }
    _INewtype DowncastClone();
  }
  public class Newtype : _INewtype {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly DAST._IType _base;
    public readonly DAST._IOptional<DAST._IExpression> _witnessExpr;
    public Newtype(Dafny.ISequence<Dafny.Rune> name, DAST._IType @base, DAST._IOptional<DAST._IExpression> witnessExpr) {
      this._name = name;
      this._base = @base;
      this._witnessExpr = witnessExpr;
    }
    public _INewtype DowncastClone() {
      if (this is _INewtype dt) { return dt; }
      return new Newtype(_name, _base, _witnessExpr);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Newtype;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._base, oth._base) && object.Equals(this._witnessExpr, oth._witnessExpr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._base));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._witnessExpr));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Newtype.Newtype";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._base);
      s += ", ";
      s += Dafny.Helpers.ToString(this._witnessExpr);
      s += ")";
      return s;
    }
    private static readonly DAST._INewtype theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, DAST.Type.Default(), DAST.Optional<DAST._IExpression>.Default());
    public static DAST._INewtype Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._INewtype> _TYPE = new Dafny.TypeDescriptor<DAST._INewtype>(DAST.Newtype.Default());
    public static Dafny.TypeDescriptor<DAST._INewtype> _TypeDescriptor() {
      return _TYPE;
    }
    public static _INewtype create(Dafny.ISequence<Dafny.Rune> name, DAST._IType @base, DAST._IOptional<DAST._IExpression> witnessExpr) {
      return new Newtype(name, @base, witnessExpr);
    }
    public static _INewtype create_Newtype(Dafny.ISequence<Dafny.Rune> name, DAST._IType @base, DAST._IOptional<DAST._IExpression> witnessExpr) {
      return create(name, @base, witnessExpr);
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
    public DAST._IOptional<DAST._IExpression> dtor_witnessExpr {
      get {
        return this._witnessExpr;
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
    bool is_NewtypeValue { get; }
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
    DAST._IType dtor_tpe { get; }
    DAST._IExpression dtor_value { get; }
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
    public static _IExpression create_NewtypeValue(DAST._IType tpe, DAST._IExpression @value) {
      return new Expression_NewtypeValue(tpe, @value);
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
    public bool is_NewtypeValue { get { return this is Expression_NewtypeValue; } }
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
    public DAST._IType dtor_tpe {
      get {
        var d = this;
        return ((Expression_NewtypeValue)d)._tpe;
      }
    }
    public DAST._IExpression dtor_value {
      get {
        var d = this;
        return ((Expression_NewtypeValue)d)._value;
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
  public class Expression_NewtypeValue : Expression {
    public readonly DAST._IType _tpe;
    public readonly DAST._IExpression _value;
    public Expression_NewtypeValue(DAST._IType tpe, DAST._IExpression @value) : base() {
      this._tpe = tpe;
      this._value = @value;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_NewtypeValue(_tpe, _value);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_NewtypeValue;
      return oth != null && object.Equals(this._tpe, oth._tpe) && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.NewtypeValue";
      s += "(";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ", ";
      s += Dafny.Helpers.ToString(this._value);
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
      hash = ((hash << 5) + hash) + 7;
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
      hash = ((hash << 5) + hash) + 8;
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
      hash = ((hash << 5) + hash) + 9;
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
      hash = ((hash << 5) + hash) + 10;
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
      hash = ((hash << 5) + hash) + 11;
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
      hash = ((hash << 5) + hash) + 12;
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
      hash = ((hash << 5) + hash) + 13;
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
      hash = ((hash << 5) + hash) + 14;
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
      hash = ((hash << 5) + hash) + 15;
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
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]\npub struct r#"), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(pub ")), _40_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ::std::default::Default for r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn default() -> Self {\n"));
      DAST._IOptional<DAST._IExpression> _source3 = (c).dtor_witnessExpr;
      if (_source3.is_Some) {
        DAST._IExpression _41___mcc_h0 = _source3.dtor_Some_a0;
        DAST._IExpression _42_e = _41___mcc_h0;
        {
          Dafny.ISequence<Dafny.Rune> _43_eStr;
          bool _44___v4;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _45___v5;
          Dafny.ISequence<Dafny.Rune> _out15;
          bool _out16;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out17;
          DCOMP.COMP.GenExpr(_42_e, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), true, out _out15, out _out16, out _out17);
          _43_eStr = _out15;
          _44___v4 = _out16;
          _45___v5 = _out17;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _43_eStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
        }
      } else {
        {
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(::std::default::Default::default())\n"));
        }
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ::dafny_runtime::DafnyPrint for r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn fmt_print(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, f)\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
      Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>> _46_ops;
      _46_ops = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::ops::Add"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add")), _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::ops::Sub"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("sub")), _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::ops::Mul"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mul")), _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::ops::Div"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("div")));
      BigInteger _47_i;
      _47_i = BigInteger.Zero;
      while ((_47_i) < (new BigInteger((_46_ops).Count))) {
        _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs0 = (_46_ops).Select(_47_i);
        Dafny.ISequence<Dafny.Rune> _48_traitName = _let_tmp_rhs0.dtor__0;
        Dafny.ISequence<Dafny.Rune> _49_methodName = _let_tmp_rhs0.dtor__1;
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _48_traitName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("> for r#")), (c).dtor_name);
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" where ")), _40_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _48_traitName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), _40_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", Output = ")), _40_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("> {\n"));
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Output = r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn ")), _49_methodName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(self, other: r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _48_traitName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _49_methodName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(self.0, other.0))\n"));
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
        _47_i = (_47_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenDatatype(DAST._IDatatype c) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _50_typeParamsSet;
      _50_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<Dafny.Rune> _51_typeParams;
      _51_typeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _52_tpI;
      _52_tpI = BigInteger.Zero;
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _51_typeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<");
        while ((_52_tpI) < (new BigInteger(((c).dtor_typeParams).Count))) {
          DAST._IType _53_tp;
          _53_tp = ((c).dtor_typeParams).Select(_52_tpI);
          _50_typeParamsSet = Dafny.Set<DAST._IType>.Union(_50_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_53_tp));
          Dafny.ISequence<Dafny.Rune> _54_genTp;
          Dafny.ISequence<Dafny.Rune> _out18;
          _out18 = DCOMP.COMP.GenType(_53_tp, false);
          _54_genTp = _out18;
          _51_typeParams = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_51_typeParams, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _54_genTp), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          _52_tpI = (_52_tpI) + (BigInteger.One);
        }
        _51_typeParams = Dafny.Sequence<Dafny.Rune>.Concat(_51_typeParams, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
      Dafny.ISequence<Dafny.Rune> _55_ctors;
      _55_ctors = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _56_i;
      _56_i = BigInteger.Zero;
      while ((_56_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _57_ctor;
        _57_ctor = ((c).dtor_ctors).Select(_56_i);
        Dafny.ISequence<Dafny.Rune> _58_ctorBody;
        _58_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), (_57_ctor).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
        BigInteger _59_j;
        _59_j = BigInteger.Zero;
        while ((_59_j) < (new BigInteger(((_57_ctor).dtor_args).Count))) {
          DAST._IFormal _60_formal;
          _60_formal = ((_57_ctor).dtor_args).Select(_59_j);
          Dafny.ISequence<Dafny.Rune> _61_formalType;
          Dafny.ISequence<Dafny.Rune> _out19;
          _out19 = DCOMP.COMP.GenType((_60_formal).dtor_typ, false);
          _61_formalType = _out19;
          if ((c).dtor_isCo) {
            _58_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_58_ctorBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_60_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::LazyFieldWrapper<")), _61_formalType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">, "));
          } else {
            _58_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_58_ctorBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_60_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _61_formalType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          _59_j = (_59_j) + (BigInteger.One);
        }
        _58_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(_58_ctorBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        _55_ctors = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_55_ctors, _58_ctorBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"));
        _56_i = (_56_i) + (BigInteger.One);
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _62_selfPath;
      _62_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<Dafny.Rune> _63_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _64_traitBodies;
      Dafny.ISequence<Dafny.Rune> _out20;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _out21;
      DCOMP.COMP.GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(_62_selfPath)), _50_typeParamsSet, out _out20, out _out21);
      _63_implBody = _out20;
      _64_traitBodies = _out21;
      _56_i = BigInteger.Zero;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _65_emittedFields;
      _65_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      while ((_56_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _66_ctor;
        _66_ctor = ((c).dtor_ctors).Select(_56_i);
        BigInteger _67_j;
        _67_j = BigInteger.Zero;
        while ((_67_j) < (new BigInteger(((_66_ctor).dtor_args).Count))) {
          DAST._IFormal _68_formal;
          _68_formal = ((_66_ctor).dtor_args).Select(_67_j);
          if (!((_65_emittedFields).Contains((_68_formal).dtor_name))) {
            _65_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_65_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_68_formal).dtor_name));
            Dafny.ISequence<Dafny.Rune> _69_formalType;
            Dafny.ISequence<Dafny.Rune> _out22;
            _out22 = DCOMP.COMP.GenType((_68_formal).dtor_typ, false);
            _69_formalType = _out22;
            Dafny.ISequence<Dafny.Rune> _70_methodBody;
            _70_methodBody = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match self {\n");
            BigInteger _71_k;
            _71_k = BigInteger.Zero;
            while ((_71_k) < (new BigInteger(((c).dtor_ctors).Count))) {
              DAST._IDatatypeCtor _72_ctor2;
              _72_ctor2 = ((c).dtor_ctors).Select(_71_k);
              Dafny.ISequence<Dafny.Rune> _73_ctorMatch;
              _73_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_72_ctor2).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
              BigInteger _74_l;
              _74_l = BigInteger.Zero;
              bool _75_hasMatchingField;
              _75_hasMatchingField = false;
              while ((_74_l) < (new BigInteger(((_72_ctor2).dtor_args).Count))) {
                DAST._IFormal _76_formal2;
                _76_formal2 = ((_72_ctor2).dtor_args).Select(_74_l);
                if (((_68_formal).dtor_name).Equals((_76_formal2).dtor_name)) {
                  _75_hasMatchingField = true;
                }
                _73_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_73_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_76_formal2).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                _74_l = (_74_l) + (BigInteger.One);
              }
              if (_75_hasMatchingField) {
                if ((c).dtor_isCo) {
                  _73_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_73_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("} => ::std::ops::Deref::deref(&")), (_68_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0),\n"));
                } else {
                  _73_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_73_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("} => ")), (_68_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"));
                }
              } else {
                _73_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(_73_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("} => panic!(\"field does not exist on this variant\"),\n"));
              }
              _70_methodBody = Dafny.Sequence<Dafny.Rune>.Concat(_70_methodBody, _73_ctorMatch);
              _71_k = (_71_k) + (BigInteger.One);
            }
            _70_methodBody = Dafny.Sequence<Dafny.Rune>.Concat(_70_methodBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            _63_implBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_63_implBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub fn r#")), (_68_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(&self) -> &")), _69_formalType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _70_methodBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
          }
          _67_j = (_67_j) + (BigInteger.One);
        }
        _56_i = (_56_i) + (BigInteger.One);
      }
      Dafny.ISequence<Dafny.Rune> _77_constrainedTypeParams;
      _77_constrainedTypeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _52_tpI = BigInteger.Zero;
        _77_constrainedTypeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<");
        while ((_52_tpI) < (new BigInteger(((c).dtor_typeParams).Count))) {
          if ((_52_tpI).Sign == 1) {
            _77_constrainedTypeParams = Dafny.Sequence<Dafny.Rune>.Concat(_77_constrainedTypeParams, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          DAST._IType _78_tp;
          _78_tp = ((c).dtor_typeParams).Select(_52_tpI);
          Dafny.ISequence<Dafny.Rune> _79_genTp;
          Dafny.ISequence<Dafny.Rune> _out23;
          _out23 = DCOMP.COMP.GenType(_78_tp, false);
          _79_genTp = _out23;
          _77_constrainedTypeParams = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_77_constrainedTypeParams, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _79_genTp), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": Clone + ::std::cmp::PartialEq + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static"));
          _52_tpI = (_52_tpI) + (BigInteger.One);
        }
        _77_constrainedTypeParams = Dafny.Sequence<Dafny.Rune>.Concat(_77_constrainedTypeParams, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
      Dafny.ISequence<Dafny.Rune> _80_enumBody;
      _80_enumBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq)]\npub enum r#"), (c).dtor_name), _51_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _55_ctors), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _77_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" r#")), (c).dtor_name), _51_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _63_implBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
      Dafny.ISequence<Dafny.Rune> _81_printImpl;
      _81_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _77_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyPrint for r#")), (c).dtor_name), _51_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn fmt_print(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match self {\n"));
      _56_i = BigInteger.Zero;
      while ((_56_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _82_ctor;
        _82_ctor = ((c).dtor_ctors).Select(_56_i);
        Dafny.ISequence<Dafny.Rune> _83_ctorMatch;
        _83_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), (_82_ctor).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
        Dafny.ISequence<Dafny.Rune> _84_modulePrefix;
        _84_modulePrefix = (((((c).dtor_enclosingModule)).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(((c).dtor_enclosingModule), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _85_printRhs;
        _85_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(f, \""), _84_modulePrefix), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), (_82_ctor).dtor_name), (((_82_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?;")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?;"))));
        BigInteger _86_j;
        _86_j = BigInteger.Zero;
        while ((_86_j) < (new BigInteger(((_82_ctor).dtor_args).Count))) {
          DAST._IFormal _87_formal;
          _87_formal = ((_82_ctor).dtor_args).Select(_86_j);
          _83_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_83_ctorMatch, (_87_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_86_j).Sign == 1) {
            _85_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(_85_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nwrite!(f, \", \")?;"));
          }
          _85_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_85_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n::dafny_runtime::DafnyPrint::fmt_print(")), (_87_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", f)?;"));
          _86_j = (_86_j) + (BigInteger.One);
        }
        _83_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(_83_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        if ((_82_ctor).dtor_hasAnyArgs) {
          _85_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(_85_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nwrite!(f, \")\")?;"));
        }
        _85_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(_85_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nOk(())"));
        _81_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_81_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _83_ctorMatch), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" => {\n")), _85_printRhs), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}\n"));
        _56_i = (_56_i) + (BigInteger.One);
      }
      _81_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(_81_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n}\n}\n"));
      Dafny.ISequence<Dafny.Rune> _88_defaultImpl;
      _88_defaultImpl = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        _88_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _77_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::std::default::Default for r#")), (c).dtor_name), _51_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn default() -> Self {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), (((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
        _56_i = BigInteger.Zero;
        while ((_56_i) < (new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count))) {
          DAST._IFormal _89_formal;
          _89_formal = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_56_i);
          _88_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_88_defaultImpl, (_89_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": std::default::Default::default(),\n"));
          _56_i = (_56_i) + (BigInteger.One);
        }
        _88_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(_88_defaultImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n}\n}\n"));
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_80_enumBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _81_printImpl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _88_defaultImpl);
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenPath(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      if ((new BigInteger((p).Count)).Sign == 0) {
        s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Self");
        return s;
      } else {
        s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super::");
        BigInteger _90_i;
        _90_i = BigInteger.Zero;
        while ((_90_i) < (new BigInteger((p).Count))) {
          if ((_90_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), ((p).Select(_90_i)));
          _90_i = (_90_i) + (BigInteger.One);
        }
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      if ((new BigInteger((args).Count)).Sign == 1) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"));
        BigInteger _91_i;
        _91_i = BigInteger.Zero;
        while ((_91_i) < (new BigInteger((args).Count))) {
          if ((_91_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          Dafny.ISequence<Dafny.Rune> _92_genTp;
          Dafny.ISequence<Dafny.Rune> _out24;
          _out24 = DCOMP.COMP.GenType((args).Select(_91_i), inBinding);
          _92_genTp = _out24;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, _92_genTp);
          _91_i = (_91_i) + (BigInteger.One);
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenType(DAST._IType c, bool inBinding) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      DAST._IType _source4 = c;
      if (_source4.is_Path) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _93___mcc_h0 = _source4.dtor_Path_a0;
        Dafny.ISequence<DAST._IType> _94___mcc_h1 = _source4.dtor_typeArgs;
        DAST._IResolvedType _95___mcc_h2 = _source4.dtor_resolved;
        DAST._IResolvedType _96_resolved = _95___mcc_h2;
        Dafny.ISequence<DAST._IType> _97_args = _94___mcc_h1;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _98_p = _93___mcc_h0;
        {
          Dafny.ISequence<Dafny.Rune> _out25;
          _out25 = DCOMP.COMP.GenPath(_98_p);
          s = _out25;
          Dafny.ISequence<Dafny.Rune> _99_typeArgs;
          Dafny.ISequence<Dafny.Rune> _out26;
          _out26 = DCOMP.COMP.GenTypeArgs(_97_args, inBinding);
          _99_typeArgs = _out26;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, _99_typeArgs);
          DAST._IResolvedType _source5 = _96_resolved;
          if (_source5.is_Datatype) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _100___mcc_h8 = _source5.dtor_path;
            {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc<"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            }
          } else if (_source5.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _101___mcc_h10 = _source5.dtor_path;
            {
              if (inBinding) {
                s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_");
              } else {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              }
            }
          } else {
            DAST._IResolvedType _102_Primitive = _96_resolved;
          }
        }
      } else if (_source4.is_Tuple) {
        Dafny.ISequence<DAST._IType> _103___mcc_h3 = _source4.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IType> _104_types = _103___mcc_h3;
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
          BigInteger _105_i;
          _105_i = BigInteger.Zero;
          while ((_105_i) < (new BigInteger((_104_types).Count))) {
            if ((_105_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
            }
            Dafny.ISequence<Dafny.Rune> _106_generated;
            Dafny.ISequence<Dafny.Rune> _out27;
            _out27 = DCOMP.COMP.GenType((_104_types).Select(_105_i), inBinding);
            _106_generated = _out27;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _106_generated), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
            _105_i = (_105_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        }
      } else if (_source4.is_Primitive) {
        DAST._IPrimitive _107___mcc_h4 = _source4.dtor_Primitive_a0;
        DAST._IPrimitive _108_p = _107___mcc_h4;
        {
          DAST._IPrimitive _source6 = _108_p;
          if (_source6.is_String) {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("String");
          } else if (_source6.is_Bool) {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool");
          } else {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char");
          }
        }
      } else if (_source4.is_Passthrough) {
        Dafny.ISequence<Dafny.Rune> _109___mcc_h5 = _source4.dtor_Passthrough_a0;
        Dafny.ISequence<Dafny.Rune> _110_v = _109___mcc_h5;
        s = _110_v;
      } else {
        Dafny.ISequence<Dafny.Rune> _111___mcc_h6 = _source4.dtor_TypeArg_a0;
        Dafny.ISequence<Dafny.Rune> _source7 = _111___mcc_h6;
        Dafny.ISequence<Dafny.Rune> _112___mcc_h7 = _source7;
        Dafny.ISequence<Dafny.Rune> _113_name = _112___mcc_h7;
        s = _113_name;
      }
      return s;
    }
    public static void GenClassImplBody(Dafny.ISequence<DAST._IClassItem> body, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams, out Dafny.ISequence<Dafny.Rune> s, out Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> traitBodies) {
      s = Dafny.Sequence<Dafny.Rune>.Empty;
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _114_i;
      _114_i = BigInteger.Zero;
      while ((_114_i) < (new BigInteger((body).Count))) {
        DAST._IClassItem _source8 = (body).Select(_114_i);
        if (_source8.is_Method) {
          DAST._IMethod _115___mcc_h0 = _source8.dtor_Method_a0;
          DAST._IMethod _116_m = _115___mcc_h0;
          {
            DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source9 = (_116_m).dtor_overridingPath;
            if (_source9.is_Some) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _117___mcc_h2 = _source9.dtor_Some_a0;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _118_p = _117___mcc_h2;
              {
                Dafny.ISequence<Dafny.Rune> _119_existing;
                _119_existing = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                if ((traitBodies).Contains(_118_p)) {
                  _119_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Select(traitBodies, _118_p);
                }
                if ((new BigInteger((_119_existing).Count)).Sign == 1) {
                  _119_existing = Dafny.Sequence<Dafny.Rune>.Concat(_119_existing, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
                }
                Dafny.ISequence<Dafny.Rune> _120_genMethod;
                Dafny.ISequence<Dafny.Rune> _out28;
                _out28 = DCOMP.COMP.GenMethod(_116_m, true, enclosingType, enclosingTypeParams);
                _120_genMethod = _out28;
                _119_existing = Dafny.Sequence<Dafny.Rune>.Concat(_119_existing, _120_genMethod);
                traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>(_118_p, _119_existing)));
              }
            } else {
              {
                Dafny.ISequence<Dafny.Rune> _121_generated;
                Dafny.ISequence<Dafny.Rune> _out29;
                _out29 = DCOMP.COMP.GenMethod(_116_m, forTrait, enclosingType, enclosingTypeParams);
                _121_generated = _out29;
                s = Dafny.Sequence<Dafny.Rune>.Concat(s, _121_generated);
              }
            }
          }
        } else {
          DAST._IFormal _122___mcc_h1 = _source8.dtor_Field_a0;
          DAST._IFormal _123_f = _122___mcc_h1;
        }
        if ((new BigInteger((s).Count)).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        _114_i = (_114_i) + (BigInteger.One);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> GenParams(Dafny.ISequence<DAST._IFormal> @params) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _124_i;
      _124_i = BigInteger.Zero;
      while ((_124_i) < (new BigInteger((@params).Count))) {
        DAST._IFormal _125_param;
        _125_param = (@params).Select(_124_i);
        Dafny.ISequence<Dafny.Rune> _126_paramType;
        Dafny.ISequence<Dafny.Rune> _out30;
        _out30 = DCOMP.COMP.GenType((_125_param).dtor_typ, false);
        _126_paramType = _out30;
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_125_param).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": &")), _126_paramType);
        if ((_124_i) < ((new BigInteger((@params).Count)) - (BigInteger.One))) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
        }
        _124_i = (_124_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISequence<Dafny.Rune> _127_params;
      Dafny.ISequence<Dafny.Rune> _out31;
      _out31 = DCOMP.COMP.GenParams((m).dtor_params);
      _127_params = _out31;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _128_paramNames;
      _128_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _129_paramI;
      _129_paramI = BigInteger.Zero;
      while ((_129_paramI) < (new BigInteger(((m).dtor_params).Count))) {
        _128_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_128_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((((m).dtor_params).Select(_129_paramI)).dtor_name));
        _129_paramI = (_129_paramI) + (BigInteger.One);
      }
      if (!((m).dtor_isStatic)) {
        if (forTrait) {
          _127_params = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _127_params);
        } else {
          Dafny.ISequence<Dafny.Rune> _130_enclosingTypeString;
          Dafny.ISequence<Dafny.Rune> _out32;
          _out32 = DCOMP.COMP.GenType(enclosingType, false);
          _130_enclosingTypeString = _out32;
          _127_params = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self: &"), _130_enclosingTypeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _127_params);
        }
      }
      Dafny.ISequence<Dafny.Rune> _131_retType;
      _131_retType = (((new BigInteger(((m).dtor_outTypes).Count)) != (BigInteger.One)) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
      BigInteger _132_typeI;
      _132_typeI = BigInteger.Zero;
      while ((_132_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        if ((_132_typeI).Sign == 1) {
          _131_retType = Dafny.Sequence<Dafny.Rune>.Concat(_131_retType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
        }
        Dafny.ISequence<Dafny.Rune> _133_typeString;
        Dafny.ISequence<Dafny.Rune> _out33;
        _out33 = DCOMP.COMP.GenType(((m).dtor_outTypes).Select(_132_typeI), false);
        _133_typeString = _out33;
        _131_retType = Dafny.Sequence<Dafny.Rune>.Concat(_131_retType, _133_typeString);
        _132_typeI = (_132_typeI) + (BigInteger.One);
      }
      if ((new BigInteger(((m).dtor_outTypes).Count)) != (BigInteger.One)) {
        _131_retType = Dafny.Sequence<Dafny.Rune>.Concat(_131_retType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      }
      if (forTrait) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn r#"), (m).dtor_name);
      } else {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub fn r#"), (m).dtor_name);
      }
      Dafny.ISequence<DAST._IType> _134_typeParamsFiltered;
      _134_typeParamsFiltered = Dafny.Sequence<DAST._IType>.FromElements();
      BigInteger _135_typeParamI;
      _135_typeParamI = BigInteger.Zero;
      while ((_135_typeParamI) < (new BigInteger(((m).dtor_typeParams).Count))) {
        DAST._IType _136_typeParam;
        _136_typeParam = ((m).dtor_typeParams).Select(_135_typeParamI);
        if (!((enclosingTypeParams).Contains(_136_typeParam))) {
          _134_typeParamsFiltered = Dafny.Sequence<DAST._IType>.Concat(_134_typeParamsFiltered, Dafny.Sequence<DAST._IType>.FromElements(_136_typeParam));
        }
        _135_typeParamI = (_135_typeParamI) + (BigInteger.One);
      }
      if ((new BigInteger((_134_typeParamsFiltered).Count)).Sign == 1) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"));
        BigInteger _137_i;
        _137_i = BigInteger.Zero;
        while ((_137_i) < (new BigInteger((_134_typeParamsFiltered).Count))) {
          if ((_137_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          Dafny.ISequence<Dafny.Rune> _138_typeString;
          Dafny.ISequence<Dafny.Rune> _out34;
          _out34 = DCOMP.COMP.GenType((_134_typeParamsFiltered).Select(_137_i), false);
          _138_typeString = _out34;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _138_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": Clone + ::std::cmp::PartialEq + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static"));
          _137_i = (_137_i) + (BigInteger.One);
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _127_params), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), _131_retType);
      if ((m).dtor_hasBody) {
        Dafny.ISequence<Dafny.Rune> _139_earlyReturn;
        _139_earlyReturn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return;");
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source10 = (m).dtor_outVars;
        if (_source10.is_Some) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _140___mcc_h0 = _source10.dtor_Some_a0;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _141_outVars = _140___mcc_h0;
          {
            _139_earlyReturn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return (");
            BigInteger _142_outI;
            _142_outI = BigInteger.Zero;
            while ((_142_outI) < (new BigInteger((_141_outVars).Count))) {
              if ((_142_outI).Sign == 1) {
                _139_earlyReturn = Dafny.Sequence<Dafny.Rune>.Concat(_139_earlyReturn, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _143_outVar;
              _143_outVar = (_141_outVars).Select(_142_outI);
              _139_earlyReturn = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_139_earlyReturn, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_143_outVar));
              _142_outI = (_142_outI) + (BigInteger.One);
            }
            _139_earlyReturn = Dafny.Sequence<Dafny.Rune>.Concat(_139_earlyReturn, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");"));
          }
        } else {
        }
        Dafny.ISequence<Dafny.Rune> _144_body;
        Dafny.ISequence<Dafny.Rune> _out35;
        _out35 = DCOMP.COMP.GenStmts((m).dtor_body, _128_paramNames, _139_earlyReturn);
        _144_body = _out35;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source11 = (m).dtor_outVars;
        if (_source11.is_Some) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _145___mcc_h1 = _source11.dtor_Some_a0;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _146_outVars = _145___mcc_h1;
          {
            _144_body = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_144_body, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _139_earlyReturn);
          }
        } else {
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _144_body), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}\n"));
      } else {
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, Dafny.ISequence<Dafny.Rune> earlyReturn) {
      Dafny.ISequence<Dafny.Rune> generated = Dafny.Sequence<Dafny.Rune>.Empty;
      generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _147_i;
      _147_i = BigInteger.Zero;
      while ((_147_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _148_stmt;
        _148_stmt = (stmts).Select(_147_i);
        Dafny.ISequence<Dafny.Rune> _149_stmtString;
        Dafny.ISequence<Dafny.Rune> _out36;
        _out36 = DCOMP.COMP.GenStmt(_148_stmt, @params, earlyReturn);
        _149_stmtString = _out36;
        if ((_147_i).Sign == 1) {
          generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, _149_stmtString);
        _147_i = (_147_i) + (BigInteger.One);
      }
      return generated;
    }
    public static Dafny.ISequence<Dafny.Rune> GenStmt(DAST._IStatement stmt, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, Dafny.ISequence<Dafny.Rune> earlyReturn) {
      Dafny.ISequence<Dafny.Rune> generated = Dafny.Sequence<Dafny.Rune>.Empty;
      DAST._IStatement _source12 = stmt;
      if (_source12.is_DeclareVar) {
        Dafny.ISequence<Dafny.Rune> _150___mcc_h0 = _source12.dtor_name;
        DAST._IType _151___mcc_h1 = _source12.dtor_typ;
        DAST._IOptional<DAST._IExpression> _152___mcc_h2 = _source12.dtor_maybeValue;
        DAST._IOptional<DAST._IExpression> _source13 = _152___mcc_h2;
        if (_source13.is_Some) {
          DAST._IExpression _153___mcc_h3 = _source13.dtor_Some_a0;
          DAST._IExpression _154_expression = _153___mcc_h3;
          DAST._IType _155_typ = _151___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _156_name = _150___mcc_h0;
          {
            Dafny.ISequence<Dafny.Rune> _157_expr;
            bool _158___v8;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _159___v9;
            Dafny.ISequence<Dafny.Rune> _out37;
            bool _out38;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out39;
            DCOMP.COMP.GenExpr(_154_expression, @params, true, out _out37, out _out38, out _out39);
            _157_expr = _out37;
            _158___v8 = _out38;
            _159___v9 = _out39;
            Dafny.ISequence<Dafny.Rune> _160_typeString;
            Dafny.ISequence<Dafny.Rune> _out40;
            _out40 = DCOMP.COMP.GenType(_155_typ, true);
            _160_typeString = _out40;
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#"), _156_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _160_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _157_expr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          }
        } else {
          DAST._IType _161_typ = _151___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _162_name = _150___mcc_h0;
          {
            Dafny.ISequence<Dafny.Rune> _163_typeString;
            Dafny.ISequence<Dafny.Rune> _out41;
            _out41 = DCOMP.COMP.GenType(_161_typ, true);
            _163_typeString = _out41;
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#"), _162_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _163_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          }
        }
      } else if (_source12.is_Assign) {
        Dafny.ISequence<Dafny.Rune> _164___mcc_h4 = _source12.dtor_name;
        DAST._IExpression _165___mcc_h5 = _source12.dtor_value;
        DAST._IExpression _166_expression = _165___mcc_h5;
        Dafny.ISequence<Dafny.Rune> _167_name = _164___mcc_h4;
        {
          Dafny.ISequence<Dafny.Rune> _168_expr;
          bool _169___v10;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _170___v11;
          Dafny.ISequence<Dafny.Rune> _out42;
          bool _out43;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out44;
          DCOMP.COMP.GenExpr(_166_expression, @params, true, out _out42, out _out43, out _out44);
          _168_expr = _out42;
          _169___v10 = _out43;
          _170___v11 = _out44;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _167_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _168_expr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
        }
      } else if (_source12.is_If) {
        DAST._IExpression _171___mcc_h6 = _source12.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _172___mcc_h7 = _source12.dtor_thn;
        Dafny.ISequence<DAST._IStatement> _173___mcc_h8 = _source12.dtor_els;
        Dafny.ISequence<DAST._IStatement> _174_els = _173___mcc_h8;
        Dafny.ISequence<DAST._IStatement> _175_thn = _172___mcc_h7;
        DAST._IExpression _176_cond = _171___mcc_h6;
        {
          Dafny.ISequence<Dafny.Rune> _177_condString;
          bool _178___v12;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _179___v13;
          Dafny.ISequence<Dafny.Rune> _out45;
          bool _out46;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out47;
          DCOMP.COMP.GenExpr(_176_cond, @params, true, out _out45, out _out46, out _out47);
          _177_condString = _out45;
          _178___v12 = _out46;
          _179___v13 = _out47;
          Dafny.ISequence<Dafny.Rune> _180_thnString;
          Dafny.ISequence<Dafny.Rune> _out48;
          _out48 = DCOMP.COMP.GenStmts(_175_thn, @params, earlyReturn);
          _180_thnString = _out48;
          Dafny.ISequence<Dafny.Rune> _181_elsString;
          Dafny.ISequence<Dafny.Rune> _out49;
          _out49 = DCOMP.COMP.GenStmts(_174_els, @params, earlyReturn);
          _181_elsString = _out49;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if "), _177_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _180_thnString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _181_elsString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
        }
      } else if (_source12.is_While) {
        DAST._IExpression _182___mcc_h9 = _source12.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _183___mcc_h10 = _source12.dtor_body;
        Dafny.ISequence<DAST._IStatement> _184_body = _183___mcc_h10;
        DAST._IExpression _185_cond = _182___mcc_h9;
        {
          Dafny.ISequence<Dafny.Rune> _186_condString;
          bool _187___v14;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _188___v15;
          Dafny.ISequence<Dafny.Rune> _out50;
          bool _out51;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out52;
          DCOMP.COMP.GenExpr(_185_cond, @params, true, out _out50, out _out51, out _out52);
          _186_condString = _out50;
          _187___v14 = _out51;
          _188___v15 = _out52;
          Dafny.ISequence<Dafny.Rune> _189_bodyString;
          Dafny.ISequence<Dafny.Rune> _out53;
          _out53 = DCOMP.COMP.GenStmts(_184_body, @params, earlyReturn);
          _189_bodyString = _out53;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while "), _186_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _189_bodyString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
        }
      } else if (_source12.is_Call) {
        DAST._IExpression _190___mcc_h11 = _source12.dtor_on;
        Dafny.ISequence<Dafny.Rune> _191___mcc_h12 = _source12.dtor_name;
        Dafny.ISequence<DAST._IType> _192___mcc_h13 = _source12.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _193___mcc_h14 = _source12.dtor_args;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _194___mcc_h15 = _source12.dtor_outs;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _195_maybeOutVars = _194___mcc_h15;
        Dafny.ISequence<DAST._IExpression> _196_args = _193___mcc_h14;
        Dafny.ISequence<DAST._IType> _197_typeArgs = _192___mcc_h13;
        Dafny.ISequence<Dafny.Rune> _198_name = _191___mcc_h12;
        DAST._IExpression _199_on = _190___mcc_h11;
        {
          Dafny.ISequence<Dafny.Rune> _200_typeArgString;
          _200_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_197_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _201_typeI;
            _201_typeI = BigInteger.Zero;
            _200_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<");
            while ((_201_typeI) < (new BigInteger((_197_typeArgs).Count))) {
              if ((_201_typeI).Sign == 1) {
                _200_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_200_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _202_typeString;
              Dafny.ISequence<Dafny.Rune> _out54;
              _out54 = DCOMP.COMP.GenType((_197_typeArgs).Select(_201_typeI), false);
              _202_typeString = _out54;
              _200_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_200_typeArgString, _202_typeString);
              _201_typeI = (_201_typeI) + (BigInteger.One);
            }
            _200_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_200_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
          Dafny.ISequence<Dafny.Rune> _203_argString;
          _203_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _204_i;
          _204_i = BigInteger.Zero;
          while ((_204_i) < (new BigInteger((_196_args).Count))) {
            if ((_204_i).Sign == 1) {
              _203_argString = Dafny.Sequence<Dafny.Rune>.Concat(_203_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _205_argExpr;
            bool _206_isOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _207___v16;
            Dafny.ISequence<Dafny.Rune> _out55;
            bool _out56;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out57;
            DCOMP.COMP.GenExpr((_196_args).Select(_204_i), @params, false, out _out55, out _out56, out _out57);
            _205_argExpr = _out55;
            _206_isOwned = _out56;
            _207___v16 = _out57;
            _203_argString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_203_argString, ((_206_isOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _205_argExpr);
            _204_i = (_204_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _208_enclosingString;
          bool _209___v17;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _210___v18;
          Dafny.ISequence<Dafny.Rune> _out58;
          bool _out59;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out60;
          DCOMP.COMP.GenExpr(_199_on, @params, true, out _out58, out _out59, out _out60);
          _208_enclosingString = _out58;
          _209___v17 = _out59;
          _210___v18 = _out60;
          DAST._IExpression _source14 = _199_on;
          if (_source14.is_Literal) {
            DAST._ILiteral _211___mcc_h18 = _source14.dtor_Literal_a0;
            {
              _208_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _208_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source14.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _212___mcc_h20 = _source14.dtor_Ident_a0;
            {
              _208_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _208_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source14.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _213___mcc_h22 = _source14.dtor_Companion_a0;
            {
              _208_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(_208_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
            }
          } else if (_source14.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _214___mcc_h24 = _source14.dtor_Tuple_a0;
            {
              _208_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _208_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source14.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _215___mcc_h26 = _source14.dtor_path;
            Dafny.ISequence<DAST._IExpression> _216___mcc_h27 = _source14.dtor_args;
            {
              _208_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _208_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source14.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _217___mcc_h30 = _source14.dtor_path;
            Dafny.ISequence<Dafny.Rune> _218___mcc_h31 = _source14.dtor_variant;
            bool _219___mcc_h32 = _source14.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _220___mcc_h33 = _source14.dtor_contents;
            {
              _208_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _208_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source14.is_NewtypeValue) {
            DAST._IType _221___mcc_h38 = _source14.dtor_tpe;
            DAST._IExpression _222___mcc_h39 = _source14.dtor_value;
            {
              _208_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _208_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source14.is_This) {
            {
              _208_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _208_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source14.is_Ite) {
            DAST._IExpression _223___mcc_h42 = _source14.dtor_cond;
            DAST._IExpression _224___mcc_h43 = _source14.dtor_thn;
            DAST._IExpression _225___mcc_h44 = _source14.dtor_els;
            {
              _208_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _208_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source14.is_UnOp) {
            DAST._IUnaryOp _226___mcc_h48 = _source14.dtor_unOp;
            DAST._IExpression _227___mcc_h49 = _source14.dtor_expr;
            {
              _208_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _208_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source14.is_BinOp) {
            Dafny.ISequence<Dafny.Rune> _228___mcc_h52 = _source14.dtor_op;
            DAST._IExpression _229___mcc_h53 = _source14.dtor_left;
            DAST._IExpression _230___mcc_h54 = _source14.dtor_right;
            {
              _208_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _208_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source14.is_Select) {
            DAST._IExpression _231___mcc_h58 = _source14.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _232___mcc_h59 = _source14.dtor_field;
            bool _233___mcc_h60 = _source14.dtor_onDatatype;
            {
              _208_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _208_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source14.is_TupleSelect) {
            DAST._IExpression _234___mcc_h64 = _source14.dtor_expr;
            BigInteger _235___mcc_h65 = _source14.dtor_index;
            {
              _208_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _208_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source14.is_Call) {
            DAST._IExpression _236___mcc_h68 = _source14.dtor_on;
            Dafny.ISequence<Dafny.Rune> _237___mcc_h69 = _source14.dtor_name;
            Dafny.ISequence<DAST._IType> _238___mcc_h70 = _source14.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _239___mcc_h71 = _source14.dtor_args;
            {
              _208_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _208_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source14.is_TypeTest) {
            DAST._IExpression _240___mcc_h76 = _source14.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _241___mcc_h77 = _source14.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _242___mcc_h78 = _source14.dtor_variant;
            {
              _208_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _208_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else {
            DAST._IType _243___mcc_h82 = _source14.dtor_typ;
            {
              _208_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _208_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          }
          Dafny.ISequence<Dafny.Rune> _244_receiver;
          _244_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source15 = _195_maybeOutVars;
          if (_source15.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _245___mcc_h84 = _source15.dtor_Some_a0;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _246_outVars = _245___mcc_h84;
            {
              if ((new BigInteger((_246_outVars).Count)) > (BigInteger.One)) {
                _244_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
              }
              BigInteger _247_outI;
              _247_outI = BigInteger.Zero;
              while ((_247_outI) < (new BigInteger((_246_outVars).Count))) {
                if ((_247_outI).Sign == 1) {
                  _244_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_244_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                Dafny.ISequence<Dafny.Rune> _248_outVar;
                _248_outVar = (_246_outVars).Select(_247_outI);
                _244_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_244_receiver, (_248_outVar));
                _247_outI = (_247_outI) + (BigInteger.One);
              }
              if ((new BigInteger((_246_outVars).Count)) > (BigInteger.One)) {
                _244_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_244_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
            }
          } else {
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((!(_244_receiver).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_244_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), _208_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _198_name), _200_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _203_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");"));
        }
      } else if (_source12.is_Return) {
        DAST._IExpression _249___mcc_h16 = _source12.dtor_expr;
        DAST._IExpression _250_expr = _249___mcc_h16;
        {
          Dafny.ISequence<Dafny.Rune> _251_exprString;
          bool _252___v21;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _253___v22;
          Dafny.ISequence<Dafny.Rune> _out61;
          bool _out62;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out63;
          DCOMP.COMP.GenExpr(_250_expr, @params, true, out _out61, out _out62, out _out63);
          _251_exprString = _out61;
          _252___v21 = _out62;
          _253___v22 = _out63;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return "), _251_exprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
        }
      } else if (_source12.is_EarlyReturn) {
        {
          generated = earlyReturn;
        }
      } else if (_source12.is_Halt) {
        {
          generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"Halt\");");
        }
      } else {
        DAST._IExpression _254___mcc_h17 = _source12.dtor_Print_a0;
        DAST._IExpression _255_e = _254___mcc_h17;
        {
          Dafny.ISequence<Dafny.Rune> _256_printedExpr;
          bool _257_isOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _258___v23;
          Dafny.ISequence<Dafny.Rune> _out64;
          bool _out65;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out66;
          DCOMP.COMP.GenExpr(_255_e, @params, false, out _out64, out _out65, out _out66);
          _256_printedExpr = _out64;
          _257_isOwned = _out65;
          _258___v23 = _out66;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper("), ((_257_isOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _256_printedExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("));"));
        }
      }
      return generated;
    }
    public static void GenExpr(DAST._IExpression e, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, bool mustOwn, out Dafny.ISequence<Dafny.Rune> s, out bool isOwned, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents) {
      s = Dafny.Sequence<Dafny.Rune>.Empty;
      isOwned = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source16 = e;
      if (_source16.is_Literal) {
        DAST._ILiteral _259___mcc_h0 = _source16.dtor_Literal_a0;
        DAST._ILiteral _source17 = _259___mcc_h0;
        if (_source17.is_BoolLiteral) {
          bool _260___mcc_h1 = _source17.dtor_BoolLiteral_a0;
          if ((_260___mcc_h1) == (false)) {
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
        } else if (_source17.is_IntLiteral) {
          BigInteger _261___mcc_h2 = _source17.dtor_IntLiteral_a0;
          BigInteger _262_i = _261___mcc_h2;
          {
            if ((_262_i).Sign == -1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-"), DCOMP.__default.natToString((BigInteger.Zero) - (_262_i)));
            } else {
              s = DCOMP.__default.natToString(_262_i);
            }
            isOwned = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source17.is_DecLiteral) {
          Dafny.ISequence<Dafny.Rune> _263___mcc_h3 = _source17.dtor_DecLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _264_l = _263___mcc_h3;
          {
            s = _264_l;
            isOwned = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else {
          Dafny.ISequence<Dafny.Rune> _265___mcc_h4 = _source17.dtor_StringLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _266_l = _265___mcc_h4;
          {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\""), _266_l), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\".to_string()"));
            isOwned = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        }
      } else if (_source16.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _267___mcc_h5 = _source16.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _268_name = _267___mcc_h5;
        {
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _268_name);
          if ((@params).Contains(_268_name)) {
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
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_268_name);
        }
      } else if (_source16.is_Companion) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _269___mcc_h6 = _source16.dtor_Companion_a0;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _270_path = _269___mcc_h6;
        {
          Dafny.ISequence<Dafny.Rune> _out67;
          _out67 = DCOMP.COMP.GenPath(_270_path);
          s = _out67;
          isOwned = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source16.is_Tuple) {
        Dafny.ISequence<DAST._IExpression> _271___mcc_h7 = _source16.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IExpression> _272_values = _271___mcc_h7;
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _273_i;
          _273_i = BigInteger.Zero;
          while ((_273_i) < (new BigInteger((_272_values).Count))) {
            if ((_273_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
            }
            Dafny.ISequence<Dafny.Rune> _274_recursiveGen;
            bool _275___v24;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _276_recIdents;
            Dafny.ISequence<Dafny.Rune> _out68;
            bool _out69;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out70;
            DCOMP.COMP.GenExpr((_272_values).Select(_273_i), @params, true, out _out68, out _out69, out _out70);
            _274_recursiveGen = _out68;
            _275___v24 = _out69;
            _276_recIdents = _out70;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _274_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _276_recIdents);
            _273_i = (_273_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
        }
      } else if (_source16.is_New) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _277___mcc_h8 = _source16.dtor_path;
        Dafny.ISequence<DAST._IExpression> _278___mcc_h9 = _source16.dtor_args;
        Dafny.ISequence<DAST._IExpression> _279_args = _278___mcc_h9;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _280_path = _277___mcc_h8;
        {
          Dafny.ISequence<Dafny.Rune> _281_path;
          Dafny.ISequence<Dafny.Rune> _out71;
          _out71 = DCOMP.COMP.GenPath(_280_path);
          _281_path = _out71;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _281_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new("));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _282_i;
          _282_i = BigInteger.Zero;
          while ((_282_i) < (new BigInteger((_279_args).Count))) {
            if ((_282_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _283_recursiveGen;
            bool _284___v25;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _285_recIdents;
            Dafny.ISequence<Dafny.Rune> _out72;
            bool _out73;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out74;
            DCOMP.COMP.GenExpr((_279_args).Select(_282_i), @params, true, out _out72, out _out73, out _out74);
            _283_recursiveGen = _out72;
            _284___v25 = _out73;
            _285_recIdents = _out74;
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _283_recursiveGen);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _285_recIdents);
            _282_i = (_282_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
        }
      } else if (_source16.is_DatatypeValue) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _286___mcc_h10 = _source16.dtor_path;
        Dafny.ISequence<Dafny.Rune> _287___mcc_h11 = _source16.dtor_variant;
        bool _288___mcc_h12 = _source16.dtor_isCo;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _289___mcc_h13 = _source16.dtor_contents;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _290_values = _289___mcc_h13;
        bool _291_isCo = _288___mcc_h12;
        Dafny.ISequence<Dafny.Rune> _292_variant = _287___mcc_h11;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _293_path = _286___mcc_h10;
        {
          Dafny.ISequence<Dafny.Rune> _294_path;
          Dafny.ISequence<Dafny.Rune> _out75;
          _out75 = DCOMP.COMP.GenPath(_293_path);
          _294_path = _out75;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _294_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _292_variant);
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _295_i;
          _295_i = BigInteger.Zero;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {"));
          while ((_295_i) < (new BigInteger((_290_values).Count))) {
            _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs1 = (_290_values).Select(_295_i);
            Dafny.ISequence<Dafny.Rune> _296_name = _let_tmp_rhs1.dtor__0;
            DAST._IExpression _297_value = _let_tmp_rhs1.dtor__1;
            if ((_295_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            if (_291_isCo) {
              Dafny.ISequence<Dafny.Rune> _298_recursiveGen;
              bool _299___v26;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _300_recIdents;
              Dafny.ISequence<Dafny.Rune> _out76;
              bool _out77;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out78;
              DCOMP.COMP.GenExpr(_297_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), true, out _out76, out _out77, out _out78);
              _298_recursiveGen = _out76;
              _299___v26 = _out77;
              _300_recIdents = _out78;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _300_recIdents);
              Dafny.ISequence<Dafny.Rune> _301_allReadCloned;
              _301_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              while (!(_300_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                Dafny.ISequence<Dafny.Rune> _302_next;
                foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_0 in (_300_recIdents).Elements) {
                  _302_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_0;
                  if ((_300_recIdents).Contains(_302_next)) {
                    goto after__ASSIGN_SUCH_THAT_0;
                  }
                }
                throw new System.Exception("assign-such-that search produced no value (line 800)");
              after__ASSIGN_SUCH_THAT_0:;
                _301_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_301_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), _302_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _302_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                _300_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_300_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_302_next));
              }
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _296_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(Box::new({\n")), _301_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), _298_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
            } else {
              Dafny.ISequence<Dafny.Rune> _303_recursiveGen;
              bool _304___v27;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _305_recIdents;
              Dafny.ISequence<Dafny.Rune> _out79;
              bool _out80;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out81;
              DCOMP.COMP.GenExpr(_297_value, @params, true, out _out79, out _out80, out _out81);
              _303_recursiveGen = _out79;
              _304___v27 = _out80;
              _305_recIdents = _out81;
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _296_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _303_recursiveGen);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _305_recIdents);
            }
            _295_i = (_295_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" })"));
          isOwned = true;
        }
      } else if (_source16.is_NewtypeValue) {
        DAST._IType _306___mcc_h14 = _source16.dtor_tpe;
        DAST._IExpression _307___mcc_h15 = _source16.dtor_value;
        DAST._IExpression _308_expr = _307___mcc_h15;
        DAST._IType _309_tpe = _306___mcc_h14;
        {
          Dafny.ISequence<Dafny.Rune> _310_typeString;
          Dafny.ISequence<Dafny.Rune> _out82;
          _out82 = DCOMP.COMP.GenType(_309_tpe, false);
          _310_typeString = _out82;
          Dafny.ISequence<Dafny.Rune> _311_recursiveGen;
          bool _312___v28;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _313_recIdents;
          Dafny.ISequence<Dafny.Rune> _out83;
          bool _out84;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out85;
          DCOMP.COMP.GenExpr(_308_expr, @params, true, out _out83, out _out84, out _out85);
          _311_recursiveGen = _out83;
          _312___v28 = _out84;
          _313_recIdents = _out85;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_310_typeString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _311_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          readIdents = _313_recIdents;
        }
      } else if (_source16.is_This) {
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
      } else if (_source16.is_Ite) {
        DAST._IExpression _314___mcc_h16 = _source16.dtor_cond;
        DAST._IExpression _315___mcc_h17 = _source16.dtor_thn;
        DAST._IExpression _316___mcc_h18 = _source16.dtor_els;
        DAST._IExpression _317_f = _316___mcc_h18;
        DAST._IExpression _318_t = _315___mcc_h17;
        DAST._IExpression _319_cond = _314___mcc_h16;
        {
          Dafny.ISequence<Dafny.Rune> _320_condString;
          bool _321___v29;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _322_recIdentsCond;
          Dafny.ISequence<Dafny.Rune> _out86;
          bool _out87;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out88;
          DCOMP.COMP.GenExpr(_319_cond, @params, true, out _out86, out _out87, out _out88);
          _320_condString = _out86;
          _321___v29 = _out87;
          _322_recIdentsCond = _out88;
          Dafny.ISequence<Dafny.Rune> _323___v30;
          bool _324_tHasToBeOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _325___v31;
          Dafny.ISequence<Dafny.Rune> _out89;
          bool _out90;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out91;
          DCOMP.COMP.GenExpr(_318_t, @params, mustOwn, out _out89, out _out90, out _out91);
          _323___v30 = _out89;
          _324_tHasToBeOwned = _out90;
          _325___v31 = _out91;
          Dafny.ISequence<Dafny.Rune> _326_fString;
          bool _327_fOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _328_recIdentsF;
          Dafny.ISequence<Dafny.Rune> _out92;
          bool _out93;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out94;
          DCOMP.COMP.GenExpr(_317_f, @params, _324_tHasToBeOwned, out _out92, out _out93, out _out94);
          _326_fString = _out92;
          _327_fOwned = _out93;
          _328_recIdentsF = _out94;
          Dafny.ISequence<Dafny.Rune> _329_tString;
          bool _330___v32;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _331_recIdentsT;
          Dafny.ISequence<Dafny.Rune> _out95;
          bool _out96;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out97;
          DCOMP.COMP.GenExpr(_318_t, @params, _327_fOwned, out _out95, out _out96, out _out97);
          _329_tString = _out95;
          _330___v32 = _out96;
          _331_recIdentsT = _out97;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _320_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _329_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _326_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})"));
          isOwned = _327_fOwned;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_322_recIdentsCond, _331_recIdentsT), _328_recIdentsF);
        }
      } else if (_source16.is_UnOp) {
        DAST._IUnaryOp _332___mcc_h19 = _source16.dtor_unOp;
        DAST._IExpression _333___mcc_h20 = _source16.dtor_expr;
        DAST._IUnaryOp _source18 = _332___mcc_h19;
        if (_source18.is_Not) {
          DAST._IExpression _334_e = _333___mcc_h20;
          {
            Dafny.ISequence<Dafny.Rune> _335_recursiveGen;
            bool _336___v33;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _337_recIdents;
            Dafny.ISequence<Dafny.Rune> _out98;
            bool _out99;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out100;
            DCOMP.COMP.GenExpr(_334_e, @params, true, out _out98, out _out99, out _out100);
            _335_recursiveGen = _out98;
            _336___v33 = _out99;
            _337_recIdents = _out100;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!("), _335_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _337_recIdents;
          }
        } else if (_source18.is_BitwiseNot) {
          DAST._IExpression _338_e = _333___mcc_h20;
          {
            Dafny.ISequence<Dafny.Rune> _339_recursiveGen;
            bool _340___v34;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _341_recIdents;
            Dafny.ISequence<Dafny.Rune> _out101;
            bool _out102;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out103;
            DCOMP.COMP.GenExpr(_338_e, @params, true, out _out101, out _out102, out _out103);
            _339_recursiveGen = _out101;
            _340___v34 = _out102;
            _341_recIdents = _out103;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~("), _339_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _341_recIdents;
          }
        } else {
          DAST._IExpression _342_e = _333___mcc_h20;
          {
            Dafny.ISequence<Dafny.Rune> _343_recursiveGen;
            bool _344___v35;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _345_recIdents;
            Dafny.ISequence<Dafny.Rune> _out104;
            bool _out105;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out106;
            DCOMP.COMP.GenExpr(_342_e, @params, false, out _out104, out _out105, out _out106);
            _343_recursiveGen = _out104;
            _344___v35 = _out105;
            _345_recIdents = _out106;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _343_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").len()"));
            isOwned = true;
            readIdents = _345_recIdents;
          }
        }
      } else if (_source16.is_BinOp) {
        Dafny.ISequence<Dafny.Rune> _346___mcc_h21 = _source16.dtor_op;
        DAST._IExpression _347___mcc_h22 = _source16.dtor_left;
        DAST._IExpression _348___mcc_h23 = _source16.dtor_right;
        DAST._IExpression _349_r = _348___mcc_h23;
        DAST._IExpression _350_l = _347___mcc_h22;
        Dafny.ISequence<Dafny.Rune> _351_op = _346___mcc_h21;
        {
          Dafny.ISequence<Dafny.Rune> _352_left;
          bool _353___v36;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _354_recIdentsL;
          Dafny.ISequence<Dafny.Rune> _out107;
          bool _out108;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out109;
          DCOMP.COMP.GenExpr(_350_l, @params, true, out _out107, out _out108, out _out109);
          _352_left = _out107;
          _353___v36 = _out108;
          _354_recIdentsL = _out109;
          Dafny.ISequence<Dafny.Rune> _355_right;
          bool _356___v37;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _357_recIdentsR;
          Dafny.ISequence<Dafny.Rune> _out110;
          bool _out111;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out112;
          DCOMP.COMP.GenExpr(_349_r, @params, true, out _out110, out _out111, out _out112);
          _355_right = _out110;
          _356___v37 = _out111;
          _357_recIdentsR = _out112;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _352_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _351_op), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _355_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_354_recIdentsL, _357_recIdentsR);
        }
      } else if (_source16.is_Select) {
        DAST._IExpression _358___mcc_h24 = _source16.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _359___mcc_h25 = _source16.dtor_field;
        bool _360___mcc_h26 = _source16.dtor_onDatatype;
        bool _361_isDatatype = _360___mcc_h26;
        Dafny.ISequence<Dafny.Rune> _362_field = _359___mcc_h25;
        DAST._IExpression _363_on = _358___mcc_h24;
        {
          Dafny.ISequence<Dafny.Rune> _364_onString;
          bool _365___v38;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _366_recIdents;
          Dafny.ISequence<Dafny.Rune> _out113;
          bool _out114;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out115;
          DCOMP.COMP.GenExpr(_363_on, @params, false, out _out113, out _out114, out _out115);
          _364_onString = _out113;
          _365___v38 = _out114;
          _366_recIdents = _out115;
          if (_361_isDatatype) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _364_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _362_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
            if (mustOwn) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            } else {
              isOwned = false;
            }
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _364_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _362_field);
            if (mustOwn) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            } else {
              isOwned = false;
            }
          }
          readIdents = _366_recIdents;
        }
      } else if (_source16.is_TupleSelect) {
        DAST._IExpression _367___mcc_h27 = _source16.dtor_expr;
        BigInteger _368___mcc_h28 = _source16.dtor_index;
        BigInteger _369_idx = _368___mcc_h28;
        DAST._IExpression _370_on = _367___mcc_h27;
        {
          Dafny.ISequence<Dafny.Rune> _371_onString;
          bool _372___v39;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _373_recIdents;
          Dafny.ISequence<Dafny.Rune> _out116;
          bool _out117;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out118;
          DCOMP.COMP.GenExpr(_370_on, @params, false, out _out116, out _out117, out _out118);
          _371_onString = _out116;
          _372___v39 = _out117;
          _373_recIdents = _out118;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _371_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").")), DCOMP.__default.natToString(_369_idx));
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
            isOwned = true;
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
            isOwned = false;
          }
          readIdents = _373_recIdents;
        }
      } else if (_source16.is_Call) {
        DAST._IExpression _374___mcc_h29 = _source16.dtor_on;
        Dafny.ISequence<Dafny.Rune> _375___mcc_h30 = _source16.dtor_name;
        Dafny.ISequence<DAST._IType> _376___mcc_h31 = _source16.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _377___mcc_h32 = _source16.dtor_args;
        Dafny.ISequence<DAST._IExpression> _378_args = _377___mcc_h32;
        Dafny.ISequence<DAST._IType> _379_typeArgs = _376___mcc_h31;
        Dafny.ISequence<Dafny.Rune> _380_name = _375___mcc_h30;
        DAST._IExpression _381_on = _374___mcc_h29;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _382_typeArgString;
          _382_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_379_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _383_typeI;
            _383_typeI = BigInteger.Zero;
            _382_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<");
            while ((_383_typeI) < (new BigInteger((_379_typeArgs).Count))) {
              if ((_383_typeI).Sign == 1) {
                _382_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_382_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _384_typeString;
              Dafny.ISequence<Dafny.Rune> _out119;
              _out119 = DCOMP.COMP.GenType((_379_typeArgs).Select(_383_typeI), false);
              _384_typeString = _out119;
              _382_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_382_typeArgString, _384_typeString);
              _383_typeI = (_383_typeI) + (BigInteger.One);
            }
            _382_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_382_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
          Dafny.ISequence<Dafny.Rune> _385_argString;
          _385_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _386_i;
          _386_i = BigInteger.Zero;
          while ((_386_i) < (new BigInteger((_378_args).Count))) {
            if ((_386_i).Sign == 1) {
              _385_argString = Dafny.Sequence<Dafny.Rune>.Concat(_385_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _387_argExpr;
            bool _388_isOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _389_recIdents;
            Dafny.ISequence<Dafny.Rune> _out120;
            bool _out121;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out122;
            DCOMP.COMP.GenExpr((_378_args).Select(_386_i), @params, false, out _out120, out _out121, out _out122);
            _387_argExpr = _out120;
            _388_isOwned = _out121;
            _389_recIdents = _out122;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _389_recIdents);
            _385_argString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_385_argString, ((_388_isOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _387_argExpr);
            _386_i = (_386_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _390_enclosingString;
          bool _391___v40;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _392_recIdents;
          Dafny.ISequence<Dafny.Rune> _out123;
          bool _out124;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out125;
          DCOMP.COMP.GenExpr(_381_on, @params, false, out _out123, out _out124, out _out125);
          _390_enclosingString = _out123;
          _391___v40 = _out124;
          _392_recIdents = _out125;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _392_recIdents);
          DAST._IExpression _source19 = _381_on;
          if (_source19.is_Literal) {
            DAST._ILiteral _393___mcc_h37 = _source19.dtor_Literal_a0;
            {
              _390_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _390_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _394___mcc_h39 = _source19.dtor_Ident_a0;
            {
              _390_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _390_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _395___mcc_h41 = _source19.dtor_Companion_a0;
            {
              _390_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(_390_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
            }
          } else if (_source19.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _396___mcc_h43 = _source19.dtor_Tuple_a0;
            {
              _390_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _390_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _397___mcc_h45 = _source19.dtor_path;
            Dafny.ISequence<DAST._IExpression> _398___mcc_h46 = _source19.dtor_args;
            {
              _390_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _390_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _399___mcc_h49 = _source19.dtor_path;
            Dafny.ISequence<Dafny.Rune> _400___mcc_h50 = _source19.dtor_variant;
            bool _401___mcc_h51 = _source19.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _402___mcc_h52 = _source19.dtor_contents;
            {
              _390_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _390_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_NewtypeValue) {
            DAST._IType _403___mcc_h57 = _source19.dtor_tpe;
            DAST._IExpression _404___mcc_h58 = _source19.dtor_value;
            {
              _390_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _390_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_This) {
            {
              _390_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _390_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Ite) {
            DAST._IExpression _405___mcc_h61 = _source19.dtor_cond;
            DAST._IExpression _406___mcc_h62 = _source19.dtor_thn;
            DAST._IExpression _407___mcc_h63 = _source19.dtor_els;
            {
              _390_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _390_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_UnOp) {
            DAST._IUnaryOp _408___mcc_h67 = _source19.dtor_unOp;
            DAST._IExpression _409___mcc_h68 = _source19.dtor_expr;
            {
              _390_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _390_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_BinOp) {
            Dafny.ISequence<Dafny.Rune> _410___mcc_h71 = _source19.dtor_op;
            DAST._IExpression _411___mcc_h72 = _source19.dtor_left;
            DAST._IExpression _412___mcc_h73 = _source19.dtor_right;
            {
              _390_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _390_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Select) {
            DAST._IExpression _413___mcc_h77 = _source19.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _414___mcc_h78 = _source19.dtor_field;
            bool _415___mcc_h79 = _source19.dtor_onDatatype;
            {
              _390_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _390_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_TupleSelect) {
            DAST._IExpression _416___mcc_h83 = _source19.dtor_expr;
            BigInteger _417___mcc_h84 = _source19.dtor_index;
            {
              _390_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _390_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Call) {
            DAST._IExpression _418___mcc_h87 = _source19.dtor_on;
            Dafny.ISequence<Dafny.Rune> _419___mcc_h88 = _source19.dtor_name;
            Dafny.ISequence<DAST._IType> _420___mcc_h89 = _source19.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _421___mcc_h90 = _source19.dtor_args;
            {
              _390_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _390_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_TypeTest) {
            DAST._IExpression _422___mcc_h95 = _source19.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _423___mcc_h96 = _source19.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _424___mcc_h97 = _source19.dtor_variant;
            {
              _390_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _390_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else {
            DAST._IType _425___mcc_h101 = _source19.dtor_typ;
            {
              _390_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _390_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_390_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _380_name), _382_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _385_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
        }
      } else if (_source16.is_TypeTest) {
        DAST._IExpression _426___mcc_h33 = _source16.dtor_on;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _427___mcc_h34 = _source16.dtor_dType;
        Dafny.ISequence<Dafny.Rune> _428___mcc_h35 = _source16.dtor_variant;
        Dafny.ISequence<Dafny.Rune> _429_variant = _428___mcc_h35;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _430_dType = _427___mcc_h34;
        DAST._IExpression _431_on = _426___mcc_h33;
        {
          Dafny.ISequence<Dafny.Rune> _432_exprGen;
          bool _433___v43;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _434_recIdents;
          Dafny.ISequence<Dafny.Rune> _out126;
          bool _out127;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out128;
          DCOMP.COMP.GenExpr(_431_on, @params, false, out _out126, out _out127, out _out128);
          _432_exprGen = _out126;
          _433___v43 = _out127;
          _434_recIdents = _out128;
          Dafny.ISequence<Dafny.Rune> _435_dTypePath;
          Dafny.ISequence<Dafny.Rune> _out129;
          _out129 = DCOMP.COMP.GenPath(_430_dType);
          _435_dTypePath = _out129;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!("), _432_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref(), ")), _435_dTypePath), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _429_variant), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. })"));
          isOwned = true;
          readIdents = _434_recIdents;
        }
      } else {
        DAST._IType _436___mcc_h36 = _source16.dtor_typ;
        DAST._IType _437_typ = _436___mcc_h36;
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
      BigInteger _438_i;
      _438_i = BigInteger.Zero;
      while ((_438_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _439_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        Dafny.ISequence<Dafny.Rune> _out130;
        _out130 = DCOMP.COMP.GenModule((p).Select(_438_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _439_generated = _out130;
        if ((_438_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _439_generated);
        _438_i = (_438_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _440_i;
      _440_i = BigInteger.Zero;
      while ((_440_i) < (new BigInteger((fullName).Count))) {
        if ((_440_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (fullName).Select(_440_i));
        _440_i = (_440_i) + (BigInteger.One);
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("();\n}"));
      return s;
    }
  }
} // end of namespace DCOMP

