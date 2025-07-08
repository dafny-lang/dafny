// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
#pragma warning disable CS0164 // This label has not been referenced
#pragma warning disable CS0162 // Unreachable code detected
#pragma warning disable CS1717 // Assignment made to same variable

namespace DAST {


  public interface _IName {
    bool is_Name { get; }
    Dafny.ISequence<Dafny.Rune> dtor_dafny__name { get; }
  }
  public class Name : _IName {
    public readonly Dafny.ISequence<Dafny.Rune> _dafny__name;
    public Name(Dafny.ISequence<Dafny.Rune> dafny__name) {
      this._dafny__name = dafny__name;
    }
    public static Dafny.ISequence<Dafny.Rune> DowncastClone(Dafny.ISequence<Dafny.Rune> _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Name;
      return oth != null && object.Equals(this._dafny__name, oth._dafny__name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._dafny__name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Name.Name";
      s += "(";
      s += this._dafny__name.ToVerbatimString(true);
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
    public static _IName create(Dafny.ISequence<Dafny.Rune> dafny__name) {
      return new Name(dafny__name);
    }
    public static _IName create_Name(Dafny.ISequence<Dafny.Rune> dafny__name) {
      return create(dafny__name);
    }
    public bool is_Name { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_dafny__name {
      get {
        return this._dafny__name;
      }
    }
  }

  public interface _IVarName {
    bool is_VarName { get; }
    Dafny.ISequence<Dafny.Rune> dtor_dafny__name { get; }
  }
  public class VarName : _IVarName {
    public readonly Dafny.ISequence<Dafny.Rune> _dafny__name;
    public VarName(Dafny.ISequence<Dafny.Rune> dafny__name) {
      this._dafny__name = dafny__name;
    }
    public static Dafny.ISequence<Dafny.Rune> DowncastClone(Dafny.ISequence<Dafny.Rune> _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as DAST.VarName;
      return oth != null && object.Equals(this._dafny__name, oth._dafny__name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._dafny__name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.VarName.VarName";
      s += "(";
      s += this._dafny__name.ToVerbatimString(true);
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
    public static _IVarName create(Dafny.ISequence<Dafny.Rune> dafny__name) {
      return new VarName(dafny__name);
    }
    public static _IVarName create_VarName(Dafny.ISequence<Dafny.Rune> dafny__name) {
      return create(dafny__name);
    }
    public bool is_VarName { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_dafny__name {
      get {
        return this._dafny__name;
      }
    }
  }

  public interface _IModule {
    bool is_Module { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<Dafny.Rune> dtor_docString { get; }
    Dafny.ISequence<DAST._IAttribute> dtor_attributes { get; }
    bool dtor_requiresExterns { get; }
    Std.Wrappers._IOption<Dafny.ISequence<DAST._IModuleItem>> dtor_body { get; }
    _IModule DowncastClone();
  }
  public class Module : _IModule {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<Dafny.Rune> _docString;
    public readonly Dafny.ISequence<DAST._IAttribute> _attributes;
    public readonly bool _requiresExterns;
    public readonly Std.Wrappers._IOption<Dafny.ISequence<DAST._IModuleItem>> _body;
    public Module(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<DAST._IAttribute> attributes, bool requiresExterns, Std.Wrappers._IOption<Dafny.ISequence<DAST._IModuleItem>> body) {
      this._name = name;
      this._docString = docString;
      this._attributes = attributes;
      this._requiresExterns = requiresExterns;
      this._body = body;
    }
    public _IModule DowncastClone() {
      if (this is _IModule dt) { return dt; }
      return new Module(_name, _docString, _attributes, _requiresExterns, _body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Module;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._docString, oth._docString) && object.Equals(this._attributes, oth._attributes) && this._requiresExterns == oth._requiresExterns && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docString));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._requiresExterns));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Module.Module";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += this._docString.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ", ";
      s += Dafny.Helpers.ToString(this._requiresExterns);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
    private static readonly DAST._IModule theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._IAttribute>.Empty, false, Std.Wrappers.Option<Dafny.ISequence<DAST._IModuleItem>>.Default());
    public static DAST._IModule Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IModule> _TYPE = new Dafny.TypeDescriptor<DAST._IModule>(DAST.Module.Default());
    public static Dafny.TypeDescriptor<DAST._IModule> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IModule create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<DAST._IAttribute> attributes, bool requiresExterns, Std.Wrappers._IOption<Dafny.ISequence<DAST._IModuleItem>> body) {
      return new Module(name, docString, attributes, requiresExterns, body);
    }
    public static _IModule create_Module(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<DAST._IAttribute> attributes, bool requiresExterns, Std.Wrappers._IOption<Dafny.ISequence<DAST._IModuleItem>> body) {
      return create(name, docString, attributes, requiresExterns, body);
    }
    public bool is_Module { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_docString {
      get {
        return this._docString;
      }
    }
    public Dafny.ISequence<DAST._IAttribute> dtor_attributes {
      get {
        return this._attributes;
      }
    }
    public bool dtor_requiresExterns {
      get {
        return this._requiresExterns;
      }
    }
    public Std.Wrappers._IOption<Dafny.ISequence<DAST._IModuleItem>> dtor_body {
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
    bool is_SynonymType { get; }
    bool is_Datatype { get; }
    DAST._IModule dtor_Module_a0 { get; }
    DAST._IClass dtor_Class_a0 { get; }
    DAST._ITrait dtor_Trait_a0 { get; }
    DAST._INewtype dtor_Newtype_a0 { get; }
    DAST._ISynonymType dtor_SynonymType_a0 { get; }
    DAST._IDatatype dtor_Datatype_a0 { get; }
    _IModuleItem DowncastClone();
    Dafny.ISequence<Dafny.Rune> name();
    Dafny.ISequence<DAST._IAttribute> attributes();
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
    public static _IModuleItem create_SynonymType(DAST._ISynonymType _a0) {
      return new ModuleItem_SynonymType(_a0);
    }
    public static _IModuleItem create_Datatype(DAST._IDatatype _a0) {
      return new ModuleItem_Datatype(_a0);
    }
    public bool is_Module { get { return this is ModuleItem_Module; } }
    public bool is_Class { get { return this is ModuleItem_Class; } }
    public bool is_Trait { get { return this is ModuleItem_Trait; } }
    public bool is_Newtype { get { return this is ModuleItem_Newtype; } }
    public bool is_SynonymType { get { return this is ModuleItem_SynonymType; } }
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
    public DAST._ISynonymType dtor_SynonymType_a0 {
      get {
        var d = this;
        return ((ModuleItem_SynonymType)d)._a0;
      }
    }
    public DAST._IDatatype dtor_Datatype_a0 {
      get {
        var d = this;
        return ((ModuleItem_Datatype)d)._a0;
      }
    }
    public abstract _IModuleItem DowncastClone();
    public Dafny.ISequence<Dafny.Rune> name() {
      DAST._IModuleItem _source0 = this;
      {
        if (_source0.is_Module) {
          DAST._IModule _0_m = _source0.dtor_Module_a0;
          return (_0_m).dtor_name;
        }
      }
      {
        if (_source0.is_Class) {
          DAST._IClass _1_m = _source0.dtor_Class_a0;
          return (_1_m).dtor_name;
        }
      }
      {
        if (_source0.is_Trait) {
          DAST._ITrait _2_m = _source0.dtor_Trait_a0;
          return (_2_m).dtor_name;
        }
      }
      {
        if (_source0.is_Newtype) {
          DAST._INewtype _3_m = _source0.dtor_Newtype_a0;
          return (_3_m).dtor_name;
        }
      }
      {
        if (_source0.is_SynonymType) {
          DAST._ISynonymType _4_m = _source0.dtor_SynonymType_a0;
          return (_4_m).dtor_name;
        }
      }
      {
        DAST._IDatatype _5_m = _source0.dtor_Datatype_a0;
        return (_5_m).dtor_name;
      }
    }
    public Dafny.ISequence<DAST._IAttribute> attributes() {
      DAST._IModuleItem _source0 = this;
      {
        if (_source0.is_Module) {
          DAST._IModule _0_m = _source0.dtor_Module_a0;
          return (_0_m).dtor_attributes;
        }
      }
      {
        if (_source0.is_Class) {
          DAST._IClass _1_m = _source0.dtor_Class_a0;
          return (_1_m).dtor_attributes;
        }
      }
      {
        if (_source0.is_Trait) {
          DAST._ITrait _2_m = _source0.dtor_Trait_a0;
          return (_2_m).dtor_attributes;
        }
      }
      {
        if (_source0.is_Newtype) {
          DAST._INewtype _3_m = _source0.dtor_Newtype_a0;
          return (_3_m).dtor_attributes;
        }
      }
      {
        if (_source0.is_SynonymType) {
          DAST._ISynonymType _4_m = _source0.dtor_SynonymType_a0;
          return (_4_m).dtor_attributes;
        }
      }
      {
        DAST._IDatatype _5_m = _source0.dtor_Datatype_a0;
        return (_5_m).dtor_attributes;
      }
    }
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
      return (int) hash;
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
      return (int) hash;
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
      return (int) hash;
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
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.ModuleItem.Newtype";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class ModuleItem_SynonymType : ModuleItem {
    public readonly DAST._ISynonymType _a0;
    public ModuleItem_SynonymType(DAST._ISynonymType _a0) : base() {
      this._a0 = _a0;
    }
    public override _IModuleItem DowncastClone() {
      if (this is _IModuleItem dt) { return dt; }
      return new ModuleItem_SynonymType(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ModuleItem_SynonymType;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.ModuleItem.SynonymType";
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
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int) hash;
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
    bool is_UserDefined { get; }
    bool is_Tuple { get; }
    bool is_Array { get; }
    bool is_Seq { get; }
    bool is_Set { get; }
    bool is_Multiset { get; }
    bool is_Map { get; }
    bool is_SetBuilder { get; }
    bool is_MapBuilder { get; }
    bool is_Arrow { get; }
    bool is_Primitive { get; }
    bool is_Passthrough { get; }
    bool is_TypeArg { get; }
    bool is_Object { get; }
    DAST._IResolvedType dtor_resolved { get; }
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
    DAST._IType Replace(Dafny.IMap<DAST._IType,DAST._IType> mapping);
    bool IsPrimitiveInt();
    bool IsGeneralTrait();
    DAST._IType GetGeneralTraitType();
    bool IsClassOrObjectTrait();
    bool IsDatatype();
    DAST._IType GetDatatypeType();
    bool Extends(DAST._IType other);
    DAST._IType RemoveSynonyms();
  }
  public abstract class Type : _IType {
    public Type() {
    }
    private static readonly DAST._IType theDefault = create_UserDefined(DAST.ResolvedType.Default());
    public static DAST._IType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IType> _TYPE = new Dafny.TypeDescriptor<DAST._IType>(DAST.Type.Default());
    public static Dafny.TypeDescriptor<DAST._IType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IType create_UserDefined(DAST._IResolvedType resolved) {
      return new Type_UserDefined(resolved);
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
    public static _IType create_SetBuilder(DAST._IType element) {
      return new Type_SetBuilder(element);
    }
    public static _IType create_MapBuilder(DAST._IType key, DAST._IType @value) {
      return new Type_MapBuilder(key, @value);
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
    public static _IType create_Object() {
      return new Type_Object();
    }
    public bool is_UserDefined { get { return this is Type_UserDefined; } }
    public bool is_Tuple { get { return this is Type_Tuple; } }
    public bool is_Array { get { return this is Type_Array; } }
    public bool is_Seq { get { return this is Type_Seq; } }
    public bool is_Set { get { return this is Type_Set; } }
    public bool is_Multiset { get { return this is Type_Multiset; } }
    public bool is_Map { get { return this is Type_Map; } }
    public bool is_SetBuilder { get { return this is Type_SetBuilder; } }
    public bool is_MapBuilder { get { return this is Type_MapBuilder; } }
    public bool is_Arrow { get { return this is Type_Arrow; } }
    public bool is_Primitive { get { return this is Type_Primitive; } }
    public bool is_Passthrough { get { return this is Type_Passthrough; } }
    public bool is_TypeArg { get { return this is Type_TypeArg; } }
    public bool is_Object { get { return this is Type_Object; } }
    public DAST._IResolvedType dtor_resolved {
      get {
        var d = this;
        return ((Type_UserDefined)d)._resolved;
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
        if (d is Type_Multiset) { return ((Type_Multiset)d)._element; }
        return ((Type_SetBuilder)d)._element;
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
        if (d is Type_Map) { return ((Type_Map)d)._key; }
        return ((Type_MapBuilder)d)._key;
      }
    }
    public DAST._IType dtor_value {
      get {
        var d = this;
        if (d is Type_Map) { return ((Type_Map)d)._value; }
        return ((Type_MapBuilder)d)._value;
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
    public DAST._IType Replace(Dafny.IMap<DAST._IType,DAST._IType> mapping) {
      if ((mapping).Contains(this)) {
        return Dafny.Map<DAST._IType, DAST._IType>.Select(mapping,this);
      } else {
        DAST._IType _source0 = this;
        {
          if (_source0.is_UserDefined) {
            DAST._IResolvedType _0_resolved = _source0.dtor_resolved;
            return DAST.Type.create_UserDefined((_0_resolved).Replace(mapping));
          }
        }
        {
          if (_source0.is_Tuple) {
            Dafny.ISequence<DAST._IType> _1_arguments = _source0.dtor_Tuple_a0;
            return DAST.Type.create_Tuple(Std.Collections.Seq.__default.Map<DAST._IType, DAST._IType>(Dafny.Helpers.Id<Func<Dafny.IMap<DAST._IType,DAST._IType>, Dafny.ISequence<DAST._IType>, Func<DAST._IType, DAST._IType>>>((_2_mapping, _3_arguments) => ((System.Func<DAST._IType, DAST._IType>)((_4_t) => {
  return (_4_t).Replace(_2_mapping);
})))(mapping, _1_arguments), _1_arguments));
          }
        }
        {
          if (_source0.is_Array) {
            DAST._IType _5_element = _source0.dtor_element;
            BigInteger _6_dims = _source0.dtor_dims;
            return DAST.Type.create_Array((_5_element).Replace(mapping), _6_dims);
          }
        }
        {
          if (_source0.is_Seq) {
            DAST._IType _7_element = _source0.dtor_element;
            return DAST.Type.create_Seq((_7_element).Replace(mapping));
          }
        }
        {
          if (_source0.is_Set) {
            DAST._IType _8_element = _source0.dtor_element;
            return DAST.Type.create_Set((_8_element).Replace(mapping));
          }
        }
        {
          if (_source0.is_Multiset) {
            DAST._IType _9_element = _source0.dtor_element;
            return DAST.Type.create_Multiset((_9_element).Replace(mapping));
          }
        }
        {
          if (_source0.is_Map) {
            DAST._IType _10_key = _source0.dtor_key;
            DAST._IType _11_value = _source0.dtor_value;
            return DAST.Type.create_Map((_10_key).Replace(mapping), (_11_value).Replace(mapping));
          }
        }
        {
          if (_source0.is_SetBuilder) {
            DAST._IType _12_element = _source0.dtor_element;
            return DAST.Type.create_SetBuilder((_12_element).Replace(mapping));
          }
        }
        {
          if (_source0.is_MapBuilder) {
            DAST._IType _13_key = _source0.dtor_key;
            DAST._IType _14_value = _source0.dtor_value;
            return DAST.Type.create_MapBuilder((_13_key).Replace(mapping), (_14_value).Replace(mapping));
          }
        }
        {
          if (_source0.is_Arrow) {
            Dafny.ISequence<DAST._IType> _15_args = _source0.dtor_args;
            DAST._IType _16_result = _source0.dtor_result;
            return DAST.Type.create_Arrow(Std.Collections.Seq.__default.Map<DAST._IType, DAST._IType>(Dafny.Helpers.Id<Func<Dafny.IMap<DAST._IType,DAST._IType>, Dafny.ISequence<DAST._IType>, Func<DAST._IType, DAST._IType>>>((_17_mapping, _18_args) => ((System.Func<DAST._IType, DAST._IType>)((_19_t) => {
  return (_19_t).Replace(_17_mapping);
})))(mapping, _15_args), _15_args), (_16_result).Replace(mapping));
          }
        }
        {
          return this;
        }
      }
    }
    public bool IsPrimitiveInt() {
      _IType _this = this;
    TAIL_CALL_START: ;
      DAST._IType _source0 = _this;
      {
        if (_source0.is_Primitive) {
          DAST._IPrimitive _h70 = _source0.dtor_Primitive_a0;
          if (_h70.is_Int) {
            return true;
          }
        }
      }
      {
        if (_source0.is_UserDefined) {
          DAST._IResolvedType resolved0 = _source0.dtor_resolved;
          DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
          if (kind0.is_SynonymType) {
            DAST._IType _0_typ = kind0.dtor_baseType;
            DAST._IType _in0 = _0_typ;
            _this = _in0;
            ;
            goto TAIL_CALL_START;
          }
        }
      }
      {
        return false;
      }
    }
    public bool IsGeneralTrait() {
      _IType _this = this;
    TAIL_CALL_START: ;
      DAST._IType _source0 = _this;
      {
        if (_source0.is_UserDefined) {
          DAST._IResolvedType resolved0 = _source0.dtor_resolved;
          DAST._IResolvedTypeBase _0_typeKind = resolved0.dtor_kind;
          DAST._IResolvedTypeBase _source1 = _0_typeKind;
          {
            if (_source1.is_SynonymType) {
              DAST._IType _1_typ = _source1.dtor_baseType;
              DAST._IType _in0 = _1_typ;
              _this = _in0;
              ;
              goto TAIL_CALL_START;
            }
          }
          {
            if (_source1.is_Trait) {
              DAST._ITraitType traitType0 = _source1.dtor_traitType;
              if (traitType0.is_GeneralTrait) {
                return true;
              }
            }
          }
          {
            return false;
          }
        }
      }
      {
        return false;
      }
    }
    public DAST._IType GetGeneralTraitType() {
      _IType _this = this;
    TAIL_CALL_START: ;
      DAST._IType _source0 = _this;
      {
        DAST._IResolvedType resolved0 = _source0.dtor_resolved;
        DAST._IResolvedTypeBase _0_typeKind = resolved0.dtor_kind;
        DAST._IResolvedTypeBase _source1 = _0_typeKind;
        {
          if (_source1.is_SynonymType) {
            DAST._IType _1_typ = _source1.dtor_baseType;
            DAST._IType _in0 = _1_typ;
            _this = _in0;
            ;
            goto TAIL_CALL_START;
          }
        }
        {
          return _this;
        }
      }
    }
    public bool IsClassOrObjectTrait() {
      DAST._IType _source0 = this;
      {
        if (_source0.is_UserDefined) {
          DAST._IResolvedType resolved0 = _source0.dtor_resolved;
          DAST._IResolvedTypeBase _0_base = resolved0.dtor_kind;
          return ((_0_base).is_Class) || (((_0_base).is_Trait) && (((_0_base).dtor_traitType).is_ObjectTrait));
        }
      }
      {
        return false;
      }
    }
    public bool IsDatatype() {
      _IType _this = this;
    TAIL_CALL_START: ;
      DAST._IType _source0 = _this;
      {
        if (_source0.is_UserDefined) {
          DAST._IResolvedType resolved0 = _source0.dtor_resolved;
          DAST._IResolvedTypeBase _0_typeKind = resolved0.dtor_kind;
          DAST._IResolvedTypeBase _source1 = _0_typeKind;
          {
            if (_source1.is_SynonymType) {
              DAST._IType _1_typ = _source1.dtor_baseType;
              DAST._IType _in0 = _1_typ;
              _this = _in0;
              ;
              goto TAIL_CALL_START;
            }
          }
          {
            if (_source1.is_Datatype) {
              return true;
            }
          }
          {
            return false;
          }
        }
      }
      {
        return false;
      }
    }
    public DAST._IType GetDatatypeType() {
      _IType _this = this;
    TAIL_CALL_START: ;
      DAST._IType _source0 = _this;
      {
        DAST._IResolvedType resolved0 = _source0.dtor_resolved;
        DAST._IResolvedTypeBase _0_typeKind = resolved0.dtor_kind;
        DAST._IResolvedTypeBase _source1 = _0_typeKind;
        {
          if (_source1.is_SynonymType) {
            DAST._IType _1_typ = _source1.dtor_baseType;
            DAST._IType _in0 = _1_typ;
            _this = _in0;
            ;
            goto TAIL_CALL_START;
          }
        }
        {
          return _this;
        }
      }
    }
    public bool Extends(DAST._IType other) {
      DAST._IType _source0 = this;
      {
        if (_source0.is_UserDefined) {
          DAST._IResolvedType resolved0 = _source0.dtor_resolved;
          Dafny.ISequence<DAST._IType> _0_extendedTypes = resolved0.dtor_extendedTypes;
          return ((_0_extendedTypes).Contains(other)) || (Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, DAST._IType, bool>>((_1_extendedTypes, _2_other) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_1_extendedTypes).Count)), false, (((_exists_var_0) => {
            BigInteger _3_i = (BigInteger)_exists_var_0;
            return (((_3_i).Sign != -1) && ((_3_i) < (new BigInteger((_1_extendedTypes).Count)))) && (((_1_extendedTypes).Select(_3_i)).Extends(_2_other));
          }))))(_0_extendedTypes, other));
        }
      }
      {
        return false;
      }
    }
    public DAST._IType RemoveSynonyms() {
      DAST._IType _source0 = this;
      {
        if (_source0.is_UserDefined) {
          DAST._IResolvedType resolved0 = _source0.dtor_resolved;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _0_path = resolved0.dtor_path;
          Dafny.ISequence<DAST._IType> _1_typeArgs = resolved0.dtor_typeArgs;
          DAST._IResolvedTypeBase _2_typeKind = resolved0.dtor_kind;
          Dafny.ISequence<DAST._IAttribute> _3_attributes = resolved0.dtor_attributes;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4_properMethods = resolved0.dtor_properMethods;
          Dafny.ISequence<DAST._IType> _5_extendedTypes = resolved0.dtor_extendedTypes;
          DAST._IResolvedTypeBase _source1 = _2_typeKind;
          {
            if (_source1.is_SynonymType) {
              DAST._IType _6_typ = _source1.dtor_baseType;
              return (_6_typ).RemoveSynonyms();
            }
          }
          {
            Dafny.ISequence<DAST._IType> _7_newtypeArgs = ((System.Func<Dafny.ISequence<DAST._IType>>) (() => {
              BigInteger dim12 = new BigInteger((_1_typeArgs).Count);
              var arr12 = new DAST._IType[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
              for (int i12 = 0; i12 < dim12; i12++) {
                var _8_i = (BigInteger) i12;
                arr12[(int)(_8_i)] = ((_1_typeArgs).Select(_8_i)).RemoveSynonyms();
              }
              return Dafny.Sequence<DAST._IType>.FromArray(arr12);
            }))();
            return DAST.Type.create_UserDefined(DAST.ResolvedType.create(_0_path, _7_newtypeArgs, _2_typeKind, _3_attributes, _4_properMethods, _5_extendedTypes));
          }
        }
      }
      {
        if (_source0.is_Tuple) {
          Dafny.ISequence<DAST._IType> _9_arguments = _source0.dtor_Tuple_a0;
          return DAST.Type.create_Tuple(Std.Collections.Seq.__default.Map<DAST._IType, DAST._IType>(Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, Func<DAST._IType, DAST._IType>>>((_10_arguments) => ((System.Func<DAST._IType, DAST._IType>)((_11_t) => {
  return (_11_t).RemoveSynonyms();
})))(_9_arguments), _9_arguments));
        }
      }
      {
        if (_source0.is_Array) {
          DAST._IType _12_element = _source0.dtor_element;
          BigInteger _13_dims = _source0.dtor_dims;
          return DAST.Type.create_Array((_12_element).RemoveSynonyms(), _13_dims);
        }
      }
      {
        if (_source0.is_Seq) {
          DAST._IType _14_element = _source0.dtor_element;
          return DAST.Type.create_Seq((_14_element).RemoveSynonyms());
        }
      }
      {
        if (_source0.is_Set) {
          DAST._IType _15_element = _source0.dtor_element;
          return DAST.Type.create_Set((_15_element).RemoveSynonyms());
        }
      }
      {
        if (_source0.is_Multiset) {
          DAST._IType _16_element = _source0.dtor_element;
          return DAST.Type.create_Multiset((_16_element).RemoveSynonyms());
        }
      }
      {
        if (_source0.is_Map) {
          DAST._IType _17_key = _source0.dtor_key;
          DAST._IType _18_value = _source0.dtor_value;
          return DAST.Type.create_Map((_17_key).RemoveSynonyms(), (_18_value).RemoveSynonyms());
        }
      }
      {
        if (_source0.is_SetBuilder) {
          DAST._IType _19_element = _source0.dtor_element;
          return DAST.Type.create_SetBuilder((_19_element).RemoveSynonyms());
        }
      }
      {
        if (_source0.is_MapBuilder) {
          DAST._IType _20_key = _source0.dtor_key;
          DAST._IType _21_value = _source0.dtor_value;
          return DAST.Type.create_MapBuilder((_20_key).RemoveSynonyms(), (_21_value).RemoveSynonyms());
        }
      }
      {
        if (_source0.is_Arrow) {
          Dafny.ISequence<DAST._IType> _22_args = _source0.dtor_args;
          DAST._IType _23_result = _source0.dtor_result;
          return DAST.Type.create_Arrow(Std.Collections.Seq.__default.Map<DAST._IType, DAST._IType>(Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, Func<DAST._IType, DAST._IType>>>((_24_args) => ((System.Func<DAST._IType, DAST._IType>)((_25_t) => {
  return (_25_t).RemoveSynonyms();
})))(_22_args), _22_args), (_23_result).RemoveSynonyms());
        }
      }
      {
        return this;
      }
    }
  }
  public class Type_UserDefined : Type {
    public readonly DAST._IResolvedType _resolved;
    public Type_UserDefined(DAST._IResolvedType resolved) : base() {
      this._resolved = resolved;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_UserDefined(_resolved);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_UserDefined;
      return oth != null && object.Equals(this._resolved, oth._resolved);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._resolved));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Type.UserDefined";
      s += "(";
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
      return (int) hash;
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
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._element));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._dims));
      return (int) hash;
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
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._element));
      return (int) hash;
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
      return (int) hash;
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
      return (int) hash;
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
      return (int) hash;
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
  public class Type_SetBuilder : Type {
    public readonly DAST._IType _element;
    public Type_SetBuilder(DAST._IType element) : base() {
      this._element = element;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_SetBuilder(_element);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_SetBuilder;
      return oth != null && object.Equals(this._element, oth._element);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._element));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Type.SetBuilder";
      s += "(";
      s += Dafny.Helpers.ToString(this._element);
      s += ")";
      return s;
    }
  }
  public class Type_MapBuilder : Type {
    public readonly DAST._IType _key;
    public readonly DAST._IType _value;
    public Type_MapBuilder(DAST._IType key, DAST._IType @value) : base() {
      this._key = key;
      this._value = @value;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_MapBuilder(_key, _value);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_MapBuilder;
      return oth != null && object.Equals(this._key, oth._key) && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Type.MapBuilder";
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
      hash = ((hash << 5) + hash) + 9;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._args));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._result));
      return (int) hash;
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
      hash = ((hash << 5) + hash) + 10;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int) hash;
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
      hash = ((hash << 5) + hash) + 11;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int) hash;
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
      hash = ((hash << 5) + hash) + 12;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Type.TypeArg";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class Type_Object : Type {
    public Type_Object() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Object();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Object;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 13;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Object";
      return s;
    }
  }

  public interface _IVariance {
    bool is_Nonvariant { get; }
    bool is_Covariant { get; }
    bool is_Contravariant { get; }
    _IVariance DowncastClone();
  }
  public abstract class Variance : _IVariance {
    public Variance() {
    }
    private static readonly DAST._IVariance theDefault = create_Nonvariant();
    public static DAST._IVariance Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IVariance> _TYPE = new Dafny.TypeDescriptor<DAST._IVariance>(DAST.Variance.Default());
    public static Dafny.TypeDescriptor<DAST._IVariance> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IVariance create_Nonvariant() {
      return new Variance_Nonvariant();
    }
    public static _IVariance create_Covariant() {
      return new Variance_Covariant();
    }
    public static _IVariance create_Contravariant() {
      return new Variance_Contravariant();
    }
    public bool is_Nonvariant { get { return this is Variance_Nonvariant; } }
    public bool is_Covariant { get { return this is Variance_Covariant; } }
    public bool is_Contravariant { get { return this is Variance_Contravariant; } }
    public static System.Collections.Generic.IEnumerable<_IVariance> AllSingletonConstructors {
      get {
        yield return Variance.create_Nonvariant();
        yield return Variance.create_Covariant();
        yield return Variance.create_Contravariant();
      }
    }
    public abstract _IVariance DowncastClone();
  }
  public class Variance_Nonvariant : Variance {
    public Variance_Nonvariant() : base() {
    }
    public override _IVariance DowncastClone() {
      if (this is _IVariance dt) { return dt; }
      return new Variance_Nonvariant();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Variance_Nonvariant;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Variance.Nonvariant";
      return s;
    }
  }
  public class Variance_Covariant : Variance {
    public Variance_Covariant() : base() {
    }
    public override _IVariance DowncastClone() {
      if (this is _IVariance dt) { return dt; }
      return new Variance_Covariant();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Variance_Covariant;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Variance.Covariant";
      return s;
    }
  }
  public class Variance_Contravariant : Variance {
    public Variance_Contravariant() : base() {
    }
    public override _IVariance DowncastClone() {
      if (this is _IVariance dt) { return dt; }
      return new Variance_Contravariant();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Variance_Contravariant;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Variance.Contravariant";
      return s;
    }
  }

  public interface _ITypeArgDecl {
    bool is_TypeArgDecl { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<DAST._ITypeArgBound> dtor_bounds { get; }
    DAST._ITypeParameterInfo dtor_info { get; }
    _ITypeArgDecl DowncastClone();
  }
  public class TypeArgDecl : _ITypeArgDecl {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<DAST._ITypeArgBound> _bounds;
    public readonly DAST._ITypeParameterInfo _info;
    public TypeArgDecl(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._ITypeArgBound> bounds, DAST._ITypeParameterInfo info) {
      this._name = name;
      this._bounds = bounds;
      this._info = info;
    }
    public _ITypeArgDecl DowncastClone() {
      if (this is _ITypeArgDecl dt) { return dt; }
      return new TypeArgDecl(_name, _bounds, _info);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.TypeArgDecl;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._bounds, oth._bounds) && object.Equals(this._info, oth._info);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._bounds));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._info));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.TypeArgDecl.TypeArgDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._bounds);
      s += ", ";
      s += Dafny.Helpers.ToString(this._info);
      s += ")";
      return s;
    }
    private static readonly DAST._ITypeArgDecl theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._ITypeArgBound>.Empty, DAST.TypeParameterInfo.Default());
    public static DAST._ITypeArgDecl Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._ITypeArgDecl> _TYPE = new Dafny.TypeDescriptor<DAST._ITypeArgDecl>(DAST.TypeArgDecl.Default());
    public static Dafny.TypeDescriptor<DAST._ITypeArgDecl> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITypeArgDecl create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._ITypeArgBound> bounds, DAST._ITypeParameterInfo info) {
      return new TypeArgDecl(name, bounds, info);
    }
    public static _ITypeArgDecl create_TypeArgDecl(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._ITypeArgBound> bounds, DAST._ITypeParameterInfo info) {
      return create(name, bounds, info);
    }
    public bool is_TypeArgDecl { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<DAST._ITypeArgBound> dtor_bounds {
      get {
        return this._bounds;
      }
    }
    public DAST._ITypeParameterInfo dtor_info {
      get {
        return this._info;
      }
    }
  }

  public interface _ITypeArgBound {
    bool is_SupportsEquality { get; }
    bool is_SupportsDefault { get; }
    bool is_TraitBound { get; }
    DAST._IType dtor_typ { get; }
    _ITypeArgBound DowncastClone();
  }
  public abstract class TypeArgBound : _ITypeArgBound {
    public TypeArgBound() {
    }
    private static readonly DAST._ITypeArgBound theDefault = create_SupportsEquality();
    public static DAST._ITypeArgBound Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._ITypeArgBound> _TYPE = new Dafny.TypeDescriptor<DAST._ITypeArgBound>(DAST.TypeArgBound.Default());
    public static Dafny.TypeDescriptor<DAST._ITypeArgBound> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITypeArgBound create_SupportsEquality() {
      return new TypeArgBound_SupportsEquality();
    }
    public static _ITypeArgBound create_SupportsDefault() {
      return new TypeArgBound_SupportsDefault();
    }
    public static _ITypeArgBound create_TraitBound(DAST._IType typ) {
      return new TypeArgBound_TraitBound(typ);
    }
    public bool is_SupportsEquality { get { return this is TypeArgBound_SupportsEquality; } }
    public bool is_SupportsDefault { get { return this is TypeArgBound_SupportsDefault; } }
    public bool is_TraitBound { get { return this is TypeArgBound_TraitBound; } }
    public DAST._IType dtor_typ {
      get {
        var d = this;
        return ((TypeArgBound_TraitBound)d)._typ;
      }
    }
    public abstract _ITypeArgBound DowncastClone();
  }
  public class TypeArgBound_SupportsEquality : TypeArgBound {
    public TypeArgBound_SupportsEquality() : base() {
    }
    public override _ITypeArgBound DowncastClone() {
      if (this is _ITypeArgBound dt) { return dt; }
      return new TypeArgBound_SupportsEquality();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.TypeArgBound_SupportsEquality;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.TypeArgBound.SupportsEquality";
      return s;
    }
  }
  public class TypeArgBound_SupportsDefault : TypeArgBound {
    public TypeArgBound_SupportsDefault() : base() {
    }
    public override _ITypeArgBound DowncastClone() {
      if (this is _ITypeArgBound dt) { return dt; }
      return new TypeArgBound_SupportsDefault();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.TypeArgBound_SupportsDefault;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.TypeArgBound.SupportsDefault";
      return s;
    }
  }
  public class TypeArgBound_TraitBound : TypeArgBound {
    public readonly DAST._IType _typ;
    public TypeArgBound_TraitBound(DAST._IType typ) : base() {
      this._typ = typ;
    }
    public override _ITypeArgBound DowncastClone() {
      if (this is _ITypeArgBound dt) { return dt; }
      return new TypeArgBound_TraitBound(_typ);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.TypeArgBound_TraitBound;
      return oth != null && object.Equals(this._typ, oth._typ);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typ));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.TypeArgBound.TraitBound";
      s += "(";
      s += Dafny.Helpers.ToString(this._typ);
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
    bool is_Native { get; }
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
    public static _IPrimitive create_Native() {
      return new Primitive_Native();
    }
    public bool is_Int { get { return this is Primitive_Int; } }
    public bool is_Real { get { return this is Primitive_Real; } }
    public bool is_String { get { return this is Primitive_String; } }
    public bool is_Bool { get { return this is Primitive_Bool; } }
    public bool is_Char { get { return this is Primitive_Char; } }
    public bool is_Native { get { return this is Primitive_Native; } }
    public static System.Collections.Generic.IEnumerable<_IPrimitive> AllSingletonConstructors {
      get {
        yield return Primitive.create_Int();
        yield return Primitive.create_Real();
        yield return Primitive.create_String();
        yield return Primitive.create_Bool();
        yield return Primitive.create_Char();
        yield return Primitive.create_Native();
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
      return (int) hash;
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
      return (int) hash;
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
      return (int) hash;
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
      return (int) hash;
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
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Primitive.Char";
      return s;
    }
  }
  public class Primitive_Native : Primitive {
    public Primitive_Native() : base() {
    }
    public override _IPrimitive DowncastClone() {
      if (this is _IPrimitive dt) { return dt; }
      return new Primitive_Native();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Primitive_Native;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Primitive.Native";
      return s;
    }
  }

  public interface _INewtypeRange {
    bool is_U8 { get; }
    bool is_I8 { get; }
    bool is_U16 { get; }
    bool is_I16 { get; }
    bool is_U32 { get; }
    bool is_I32 { get; }
    bool is_U64 { get; }
    bool is_I64 { get; }
    bool is_U128 { get; }
    bool is_I128 { get; }
    bool is_NativeArrayIndex { get; }
    bool is_BigInt { get; }
    bool is_Bool { get; }
    bool is_Sequence { get; }
    bool is_Map { get; }
    bool is_NoRange { get; }
    bool dtor_overflow { get; }
    _INewtypeRange DowncastClone();
    bool CanOverflow();
    bool HasArithmeticOperations();
  }
  public abstract class NewtypeRange : _INewtypeRange {
    public NewtypeRange() {
    }
    private static readonly DAST._INewtypeRange theDefault = create_U8(false);
    public static DAST._INewtypeRange Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._INewtypeRange> _TYPE = new Dafny.TypeDescriptor<DAST._INewtypeRange>(DAST.NewtypeRange.Default());
    public static Dafny.TypeDescriptor<DAST._INewtypeRange> _TypeDescriptor() {
      return _TYPE;
    }
    public static _INewtypeRange create_U8(bool overflow) {
      return new NewtypeRange_U8(overflow);
    }
    public static _INewtypeRange create_I8(bool overflow) {
      return new NewtypeRange_I8(overflow);
    }
    public static _INewtypeRange create_U16(bool overflow) {
      return new NewtypeRange_U16(overflow);
    }
    public static _INewtypeRange create_I16(bool overflow) {
      return new NewtypeRange_I16(overflow);
    }
    public static _INewtypeRange create_U32(bool overflow) {
      return new NewtypeRange_U32(overflow);
    }
    public static _INewtypeRange create_I32(bool overflow) {
      return new NewtypeRange_I32(overflow);
    }
    public static _INewtypeRange create_U64(bool overflow) {
      return new NewtypeRange_U64(overflow);
    }
    public static _INewtypeRange create_I64(bool overflow) {
      return new NewtypeRange_I64(overflow);
    }
    public static _INewtypeRange create_U128(bool overflow) {
      return new NewtypeRange_U128(overflow);
    }
    public static _INewtypeRange create_I128(bool overflow) {
      return new NewtypeRange_I128(overflow);
    }
    public static _INewtypeRange create_NativeArrayIndex() {
      return new NewtypeRange_NativeArrayIndex();
    }
    public static _INewtypeRange create_BigInt() {
      return new NewtypeRange_BigInt();
    }
    public static _INewtypeRange create_Bool() {
      return new NewtypeRange_Bool();
    }
    public static _INewtypeRange create_Sequence() {
      return new NewtypeRange_Sequence();
    }
    public static _INewtypeRange create_Map() {
      return new NewtypeRange_Map();
    }
    public static _INewtypeRange create_NoRange() {
      return new NewtypeRange_NoRange();
    }
    public bool is_U8 { get { return this is NewtypeRange_U8; } }
    public bool is_I8 { get { return this is NewtypeRange_I8; } }
    public bool is_U16 { get { return this is NewtypeRange_U16; } }
    public bool is_I16 { get { return this is NewtypeRange_I16; } }
    public bool is_U32 { get { return this is NewtypeRange_U32; } }
    public bool is_I32 { get { return this is NewtypeRange_I32; } }
    public bool is_U64 { get { return this is NewtypeRange_U64; } }
    public bool is_I64 { get { return this is NewtypeRange_I64; } }
    public bool is_U128 { get { return this is NewtypeRange_U128; } }
    public bool is_I128 { get { return this is NewtypeRange_I128; } }
    public bool is_NativeArrayIndex { get { return this is NewtypeRange_NativeArrayIndex; } }
    public bool is_BigInt { get { return this is NewtypeRange_BigInt; } }
    public bool is_Bool { get { return this is NewtypeRange_Bool; } }
    public bool is_Sequence { get { return this is NewtypeRange_Sequence; } }
    public bool is_Map { get { return this is NewtypeRange_Map; } }
    public bool is_NoRange { get { return this is NewtypeRange_NoRange; } }
    public bool dtor_overflow {
      get {
        var d = this;
        if (d is NewtypeRange_U8) { return ((NewtypeRange_U8)d)._overflow; }
        if (d is NewtypeRange_I8) { return ((NewtypeRange_I8)d)._overflow; }
        if (d is NewtypeRange_U16) { return ((NewtypeRange_U16)d)._overflow; }
        if (d is NewtypeRange_I16) { return ((NewtypeRange_I16)d)._overflow; }
        if (d is NewtypeRange_U32) { return ((NewtypeRange_U32)d)._overflow; }
        if (d is NewtypeRange_I32) { return ((NewtypeRange_I32)d)._overflow; }
        if (d is NewtypeRange_U64) { return ((NewtypeRange_U64)d)._overflow; }
        if (d is NewtypeRange_I64) { return ((NewtypeRange_I64)d)._overflow; }
        if (d is NewtypeRange_U128) { return ((NewtypeRange_U128)d)._overflow; }
        return ((NewtypeRange_I128)d)._overflow;
      }
    }
    public abstract _INewtypeRange DowncastClone();
    public bool CanOverflow() {
      return (((((((((((this).is_U8) || ((this).is_I8)) || ((this).is_U16)) || ((this).is_I16)) || ((this).is_U32)) || ((this).is_I32)) || ((this).is_U64)) || ((this).is_I64)) || ((this).is_U128)) || ((this).is_I128)) && ((this).dtor_overflow);
    }
    public bool HasArithmeticOperations() {
      return ((!((this).is_Bool)) && (!((this).is_Map))) && (!((this).is_Sequence));
    }
  }
  public class NewtypeRange_U8 : NewtypeRange {
    public readonly bool _overflow;
    public NewtypeRange_U8(bool overflow) : base() {
      this._overflow = overflow;
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_U8(_overflow);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_U8;
      return oth != null && this._overflow == oth._overflow;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overflow));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.U8";
      s += "(";
      s += Dafny.Helpers.ToString(this._overflow);
      s += ")";
      return s;
    }
  }
  public class NewtypeRange_I8 : NewtypeRange {
    public readonly bool _overflow;
    public NewtypeRange_I8(bool overflow) : base() {
      this._overflow = overflow;
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_I8(_overflow);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_I8;
      return oth != null && this._overflow == oth._overflow;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overflow));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.I8";
      s += "(";
      s += Dafny.Helpers.ToString(this._overflow);
      s += ")";
      return s;
    }
  }
  public class NewtypeRange_U16 : NewtypeRange {
    public readonly bool _overflow;
    public NewtypeRange_U16(bool overflow) : base() {
      this._overflow = overflow;
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_U16(_overflow);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_U16;
      return oth != null && this._overflow == oth._overflow;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overflow));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.U16";
      s += "(";
      s += Dafny.Helpers.ToString(this._overflow);
      s += ")";
      return s;
    }
  }
  public class NewtypeRange_I16 : NewtypeRange {
    public readonly bool _overflow;
    public NewtypeRange_I16(bool overflow) : base() {
      this._overflow = overflow;
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_I16(_overflow);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_I16;
      return oth != null && this._overflow == oth._overflow;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overflow));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.I16";
      s += "(";
      s += Dafny.Helpers.ToString(this._overflow);
      s += ")";
      return s;
    }
  }
  public class NewtypeRange_U32 : NewtypeRange {
    public readonly bool _overflow;
    public NewtypeRange_U32(bool overflow) : base() {
      this._overflow = overflow;
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_U32(_overflow);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_U32;
      return oth != null && this._overflow == oth._overflow;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overflow));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.U32";
      s += "(";
      s += Dafny.Helpers.ToString(this._overflow);
      s += ")";
      return s;
    }
  }
  public class NewtypeRange_I32 : NewtypeRange {
    public readonly bool _overflow;
    public NewtypeRange_I32(bool overflow) : base() {
      this._overflow = overflow;
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_I32(_overflow);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_I32;
      return oth != null && this._overflow == oth._overflow;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overflow));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.I32";
      s += "(";
      s += Dafny.Helpers.ToString(this._overflow);
      s += ")";
      return s;
    }
  }
  public class NewtypeRange_U64 : NewtypeRange {
    public readonly bool _overflow;
    public NewtypeRange_U64(bool overflow) : base() {
      this._overflow = overflow;
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_U64(_overflow);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_U64;
      return oth != null && this._overflow == oth._overflow;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overflow));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.U64";
      s += "(";
      s += Dafny.Helpers.ToString(this._overflow);
      s += ")";
      return s;
    }
  }
  public class NewtypeRange_I64 : NewtypeRange {
    public readonly bool _overflow;
    public NewtypeRange_I64(bool overflow) : base() {
      this._overflow = overflow;
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_I64(_overflow);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_I64;
      return oth != null && this._overflow == oth._overflow;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overflow));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.I64";
      s += "(";
      s += Dafny.Helpers.ToString(this._overflow);
      s += ")";
      return s;
    }
  }
  public class NewtypeRange_U128 : NewtypeRange {
    public readonly bool _overflow;
    public NewtypeRange_U128(bool overflow) : base() {
      this._overflow = overflow;
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_U128(_overflow);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_U128;
      return oth != null && this._overflow == oth._overflow;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overflow));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.U128";
      s += "(";
      s += Dafny.Helpers.ToString(this._overflow);
      s += ")";
      return s;
    }
  }
  public class NewtypeRange_I128 : NewtypeRange {
    public readonly bool _overflow;
    public NewtypeRange_I128(bool overflow) : base() {
      this._overflow = overflow;
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_I128(_overflow);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_I128;
      return oth != null && this._overflow == oth._overflow;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overflow));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.I128";
      s += "(";
      s += Dafny.Helpers.ToString(this._overflow);
      s += ")";
      return s;
    }
  }
  public class NewtypeRange_NativeArrayIndex : NewtypeRange {
    public NewtypeRange_NativeArrayIndex() : base() {
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_NativeArrayIndex();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_NativeArrayIndex;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 10;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.NativeArrayIndex";
      return s;
    }
  }
  public class NewtypeRange_BigInt : NewtypeRange {
    public NewtypeRange_BigInt() : base() {
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_BigInt();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_BigInt;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 11;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.BigInt";
      return s;
    }
  }
  public class NewtypeRange_Bool : NewtypeRange {
    public NewtypeRange_Bool() : base() {
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_Bool();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_Bool;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 12;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.Bool";
      return s;
    }
  }
  public class NewtypeRange_Sequence : NewtypeRange {
    public NewtypeRange_Sequence() : base() {
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_Sequence();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_Sequence;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 13;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.Sequence";
      return s;
    }
  }
  public class NewtypeRange_Map : NewtypeRange {
    public NewtypeRange_Map() : base() {
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_Map();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_Map;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 14;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.Map";
      return s;
    }
  }
  public class NewtypeRange_NoRange : NewtypeRange {
    public NewtypeRange_NoRange() : base() {
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_NoRange();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_NoRange;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 15;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.NoRange";
      return s;
    }
  }

  public interface _IAttribute {
    bool is_Attribute { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_args { get; }
    _IAttribute DowncastClone();
  }
  public class Attribute : _IAttribute {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _args;
    public Attribute(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> args) {
      this._name = name;
      this._args = args;
    }
    public _IAttribute DowncastClone() {
      if (this is _IAttribute dt) { return dt; }
      return new Attribute(_name, _args);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Attribute;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._args, oth._args);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._args));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Attribute.Attribute";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._args);
      s += ")";
      return s;
    }
    private static readonly DAST._IAttribute theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Empty);
    public static DAST._IAttribute Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IAttribute> _TYPE = new Dafny.TypeDescriptor<DAST._IAttribute>(DAST.Attribute.Default());
    public static Dafny.TypeDescriptor<DAST._IAttribute> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAttribute create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> args) {
      return new Attribute(name, args);
    }
    public static _IAttribute create_Attribute(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> args) {
      return create(name, args);
    }
    public bool is_Attribute { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_args {
      get {
        return this._args;
      }
    }
  }

  public interface _INewtypeType {
    bool is_NewtypeType { get; }
    DAST._IType dtor_baseType { get; }
    DAST._INewtypeRange dtor_range { get; }
    bool dtor_erase { get; }
    _INewtypeType DowncastClone();
  }
  public class NewtypeType : _INewtypeType {
    public readonly DAST._IType _baseType;
    public readonly DAST._INewtypeRange _range;
    public readonly bool _erase;
    public NewtypeType(DAST._IType baseType, DAST._INewtypeRange range, bool erase) {
      this._baseType = baseType;
      this._range = range;
      this._erase = erase;
    }
    public _INewtypeType DowncastClone() {
      if (this is _INewtypeType dt) { return dt; }
      return new NewtypeType(_baseType, _range, _erase);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeType;
      return oth != null && object.Equals(this._baseType, oth._baseType) && object.Equals(this._range, oth._range) && this._erase == oth._erase;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._baseType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._range));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._erase));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeType.NewtypeType";
      s += "(";
      s += Dafny.Helpers.ToString(this._baseType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._range);
      s += ", ";
      s += Dafny.Helpers.ToString(this._erase);
      s += ")";
      return s;
    }
    private static readonly DAST._INewtypeType theDefault = create(DAST.Type.Default(), DAST.NewtypeRange.Default(), false);
    public static DAST._INewtypeType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._INewtypeType> _TYPE = new Dafny.TypeDescriptor<DAST._INewtypeType>(DAST.NewtypeType.Default());
    public static Dafny.TypeDescriptor<DAST._INewtypeType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _INewtypeType create(DAST._IType baseType, DAST._INewtypeRange range, bool erase) {
      return new NewtypeType(baseType, range, erase);
    }
    public static _INewtypeType create_NewtypeType(DAST._IType baseType, DAST._INewtypeRange range, bool erase) {
      return create(baseType, range, erase);
    }
    public bool is_NewtypeType { get { return true; } }
    public DAST._IType dtor_baseType {
      get {
        return this._baseType;
      }
    }
    public DAST._INewtypeRange dtor_range {
      get {
        return this._range;
      }
    }
    public bool dtor_erase {
      get {
        return this._erase;
      }
    }
  }

  public interface _ITraitType {
    bool is_ObjectTrait { get; }
    bool is_GeneralTrait { get; }
    _ITraitType DowncastClone();
  }
  public abstract class TraitType : _ITraitType {
    public TraitType() {
    }
    private static readonly DAST._ITraitType theDefault = create_ObjectTrait();
    public static DAST._ITraitType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._ITraitType> _TYPE = new Dafny.TypeDescriptor<DAST._ITraitType>(DAST.TraitType.Default());
    public static Dafny.TypeDescriptor<DAST._ITraitType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITraitType create_ObjectTrait() {
      return new TraitType_ObjectTrait();
    }
    public static _ITraitType create_GeneralTrait() {
      return new TraitType_GeneralTrait();
    }
    public bool is_ObjectTrait { get { return this is TraitType_ObjectTrait; } }
    public bool is_GeneralTrait { get { return this is TraitType_GeneralTrait; } }
    public static System.Collections.Generic.IEnumerable<_ITraitType> AllSingletonConstructors {
      get {
        yield return TraitType.create_ObjectTrait();
        yield return TraitType.create_GeneralTrait();
      }
    }
    public abstract _ITraitType DowncastClone();
  }
  public class TraitType_ObjectTrait : TraitType {
    public TraitType_ObjectTrait() : base() {
    }
    public override _ITraitType DowncastClone() {
      if (this is _ITraitType dt) { return dt; }
      return new TraitType_ObjectTrait();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.TraitType_ObjectTrait;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.TraitType.ObjectTrait";
      return s;
    }
  }
  public class TraitType_GeneralTrait : TraitType {
    public TraitType_GeneralTrait() : base() {
    }
    public override _ITraitType DowncastClone() {
      if (this is _ITraitType dt) { return dt; }
      return new TraitType_GeneralTrait();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.TraitType_GeneralTrait;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.TraitType.GeneralTrait";
      return s;
    }
  }

  public interface _ITypeParameterInfo {
    bool is_TypeParameterInfo { get; }
    DAST._IVariance dtor_variance { get; }
    bool dtor_necessaryForEqualitySupportOfSurroundingInductiveDatatype { get; }
    _ITypeParameterInfo DowncastClone();
  }
  public class TypeParameterInfo : _ITypeParameterInfo {
    public readonly DAST._IVariance _variance;
    public readonly bool _necessaryForEqualitySupportOfSurroundingInductiveDatatype;
    public TypeParameterInfo(DAST._IVariance variance, bool necessaryForEqualitySupportOfSurroundingInductiveDatatype) {
      this._variance = variance;
      this._necessaryForEqualitySupportOfSurroundingInductiveDatatype = necessaryForEqualitySupportOfSurroundingInductiveDatatype;
    }
    public _ITypeParameterInfo DowncastClone() {
      if (this is _ITypeParameterInfo dt) { return dt; }
      return new TypeParameterInfo(_variance, _necessaryForEqualitySupportOfSurroundingInductiveDatatype);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.TypeParameterInfo;
      return oth != null && object.Equals(this._variance, oth._variance) && this._necessaryForEqualitySupportOfSurroundingInductiveDatatype == oth._necessaryForEqualitySupportOfSurroundingInductiveDatatype;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._variance));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._necessaryForEqualitySupportOfSurroundingInductiveDatatype));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.TypeParameterInfo.TypeParameterInfo";
      s += "(";
      s += Dafny.Helpers.ToString(this._variance);
      s += ", ";
      s += Dafny.Helpers.ToString(this._necessaryForEqualitySupportOfSurroundingInductiveDatatype);
      s += ")";
      return s;
    }
    private static readonly DAST._ITypeParameterInfo theDefault = create(DAST.Variance.Default(), false);
    public static DAST._ITypeParameterInfo Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._ITypeParameterInfo> _TYPE = new Dafny.TypeDescriptor<DAST._ITypeParameterInfo>(DAST.TypeParameterInfo.Default());
    public static Dafny.TypeDescriptor<DAST._ITypeParameterInfo> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITypeParameterInfo create(DAST._IVariance variance, bool necessaryForEqualitySupportOfSurroundingInductiveDatatype) {
      return new TypeParameterInfo(variance, necessaryForEqualitySupportOfSurroundingInductiveDatatype);
    }
    public static _ITypeParameterInfo create_TypeParameterInfo(DAST._IVariance variance, bool necessaryForEqualitySupportOfSurroundingInductiveDatatype) {
      return create(variance, necessaryForEqualitySupportOfSurroundingInductiveDatatype);
    }
    public bool is_TypeParameterInfo { get { return true; } }
    public DAST._IVariance dtor_variance {
      get {
        return this._variance;
      }
    }
    public bool dtor_necessaryForEqualitySupportOfSurroundingInductiveDatatype {
      get {
        return this._necessaryForEqualitySupportOfSurroundingInductiveDatatype;
      }
    }
  }

  public interface _IEqualitySupport {
    bool is_Never { get; }
    bool is_ConsultTypeArguments { get; }
    _IEqualitySupport DowncastClone();
  }
  public abstract class EqualitySupport : _IEqualitySupport {
    public EqualitySupport() {
    }
    private static readonly DAST._IEqualitySupport theDefault = create_Never();
    public static DAST._IEqualitySupport Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IEqualitySupport> _TYPE = new Dafny.TypeDescriptor<DAST._IEqualitySupport>(DAST.EqualitySupport.Default());
    public static Dafny.TypeDescriptor<DAST._IEqualitySupport> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEqualitySupport create_Never() {
      return new EqualitySupport_Never();
    }
    public static _IEqualitySupport create_ConsultTypeArguments() {
      return new EqualitySupport_ConsultTypeArguments();
    }
    public bool is_Never { get { return this is EqualitySupport_Never; } }
    public bool is_ConsultTypeArguments { get { return this is EqualitySupport_ConsultTypeArguments; } }
    public static System.Collections.Generic.IEnumerable<_IEqualitySupport> AllSingletonConstructors {
      get {
        yield return EqualitySupport.create_Never();
        yield return EqualitySupport.create_ConsultTypeArguments();
      }
    }
    public abstract _IEqualitySupport DowncastClone();
  }
  public class EqualitySupport_Never : EqualitySupport {
    public EqualitySupport_Never() : base() {
    }
    public override _IEqualitySupport DowncastClone() {
      if (this is _IEqualitySupport dt) { return dt; }
      return new EqualitySupport_Never();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.EqualitySupport_Never;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.EqualitySupport.Never";
      return s;
    }
  }
  public class EqualitySupport_ConsultTypeArguments : EqualitySupport {
    public EqualitySupport_ConsultTypeArguments() : base() {
    }
    public override _IEqualitySupport DowncastClone() {
      if (this is _IEqualitySupport dt) { return dt; }
      return new EqualitySupport_ConsultTypeArguments();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.EqualitySupport_ConsultTypeArguments;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.EqualitySupport.ConsultTypeArguments";
      return s;
    }
  }

  public interface _IResolvedTypeBase {
    bool is_Class { get; }
    bool is_Datatype { get; }
    bool is_Trait { get; }
    bool is_SynonymType { get; }
    bool is_Newtype { get; }
    DAST._IEqualitySupport dtor_equalitySupport { get; }
    Dafny.ISequence<DAST._ITypeParameterInfo> dtor_info { get; }
    DAST._ITraitType dtor_traitType { get; }
    DAST._IType dtor_baseType { get; }
    DAST._INewtypeRange dtor_range { get; }
    bool dtor_erase { get; }
    _IResolvedTypeBase DowncastClone();
  }
  public abstract class ResolvedTypeBase : _IResolvedTypeBase {
    public ResolvedTypeBase() {
    }
    private static readonly DAST._IResolvedTypeBase theDefault = create_Class();
    public static DAST._IResolvedTypeBase Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IResolvedTypeBase> _TYPE = new Dafny.TypeDescriptor<DAST._IResolvedTypeBase>(DAST.ResolvedTypeBase.Default());
    public static Dafny.TypeDescriptor<DAST._IResolvedTypeBase> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IResolvedTypeBase create_Class() {
      return new ResolvedTypeBase_Class();
    }
    public static _IResolvedTypeBase create_Datatype(DAST._IEqualitySupport equalitySupport, Dafny.ISequence<DAST._ITypeParameterInfo> info) {
      return new ResolvedTypeBase_Datatype(equalitySupport, info);
    }
    public static _IResolvedTypeBase create_Trait(DAST._ITraitType traitType) {
      return new ResolvedTypeBase_Trait(traitType);
    }
    public static _IResolvedTypeBase create_SynonymType(DAST._IType baseType) {
      return new ResolvedTypeBase_SynonymType(baseType);
    }
    public static _IResolvedTypeBase create_Newtype(DAST._IType baseType, DAST._INewtypeRange range, bool erase) {
      return new ResolvedTypeBase_Newtype(baseType, range, erase);
    }
    public bool is_Class { get { return this is ResolvedTypeBase_Class; } }
    public bool is_Datatype { get { return this is ResolvedTypeBase_Datatype; } }
    public bool is_Trait { get { return this is ResolvedTypeBase_Trait; } }
    public bool is_SynonymType { get { return this is ResolvedTypeBase_SynonymType; } }
    public bool is_Newtype { get { return this is ResolvedTypeBase_Newtype; } }
    public DAST._IEqualitySupport dtor_equalitySupport {
      get {
        var d = this;
        return ((ResolvedTypeBase_Datatype)d)._equalitySupport;
      }
    }
    public Dafny.ISequence<DAST._ITypeParameterInfo> dtor_info {
      get {
        var d = this;
        return ((ResolvedTypeBase_Datatype)d)._info;
      }
    }
    public DAST._ITraitType dtor_traitType {
      get {
        var d = this;
        return ((ResolvedTypeBase_Trait)d)._traitType;
      }
    }
    public DAST._IType dtor_baseType {
      get {
        var d = this;
        if (d is ResolvedTypeBase_SynonymType) { return ((ResolvedTypeBase_SynonymType)d)._baseType; }
        return ((ResolvedTypeBase_Newtype)d)._baseType;
      }
    }
    public DAST._INewtypeRange dtor_range {
      get {
        var d = this;
        return ((ResolvedTypeBase_Newtype)d)._range;
      }
    }
    public bool dtor_erase {
      get {
        var d = this;
        return ((ResolvedTypeBase_Newtype)d)._erase;
      }
    }
    public abstract _IResolvedTypeBase DowncastClone();
  }
  public class ResolvedTypeBase_Class : ResolvedTypeBase {
    public ResolvedTypeBase_Class() : base() {
    }
    public override _IResolvedTypeBase DowncastClone() {
      if (this is _IResolvedTypeBase dt) { return dt; }
      return new ResolvedTypeBase_Class();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ResolvedTypeBase_Class;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.ResolvedTypeBase.Class";
      return s;
    }
  }
  public class ResolvedTypeBase_Datatype : ResolvedTypeBase {
    public readonly DAST._IEqualitySupport _equalitySupport;
    public readonly Dafny.ISequence<DAST._ITypeParameterInfo> _info;
    public ResolvedTypeBase_Datatype(DAST._IEqualitySupport equalitySupport, Dafny.ISequence<DAST._ITypeParameterInfo> info) : base() {
      this._equalitySupport = equalitySupport;
      this._info = info;
    }
    public override _IResolvedTypeBase DowncastClone() {
      if (this is _IResolvedTypeBase dt) { return dt; }
      return new ResolvedTypeBase_Datatype(_equalitySupport, _info);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ResolvedTypeBase_Datatype;
      return oth != null && object.Equals(this._equalitySupport, oth._equalitySupport) && object.Equals(this._info, oth._info);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._equalitySupport));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._info));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.ResolvedTypeBase.Datatype";
      s += "(";
      s += Dafny.Helpers.ToString(this._equalitySupport);
      s += ", ";
      s += Dafny.Helpers.ToString(this._info);
      s += ")";
      return s;
    }
  }
  public class ResolvedTypeBase_Trait : ResolvedTypeBase {
    public readonly DAST._ITraitType _traitType;
    public ResolvedTypeBase_Trait(DAST._ITraitType traitType) : base() {
      this._traitType = traitType;
    }
    public override _IResolvedTypeBase DowncastClone() {
      if (this is _IResolvedTypeBase dt) { return dt; }
      return new ResolvedTypeBase_Trait(_traitType);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ResolvedTypeBase_Trait;
      return oth != null && object.Equals(this._traitType, oth._traitType);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._traitType));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.ResolvedTypeBase.Trait";
      s += "(";
      s += Dafny.Helpers.ToString(this._traitType);
      s += ")";
      return s;
    }
  }
  public class ResolvedTypeBase_SynonymType : ResolvedTypeBase {
    public readonly DAST._IType _baseType;
    public ResolvedTypeBase_SynonymType(DAST._IType baseType) : base() {
      this._baseType = baseType;
    }
    public override _IResolvedTypeBase DowncastClone() {
      if (this is _IResolvedTypeBase dt) { return dt; }
      return new ResolvedTypeBase_SynonymType(_baseType);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ResolvedTypeBase_SynonymType;
      return oth != null && object.Equals(this._baseType, oth._baseType);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._baseType));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.ResolvedTypeBase.SynonymType";
      s += "(";
      s += Dafny.Helpers.ToString(this._baseType);
      s += ")";
      return s;
    }
  }
  public class ResolvedTypeBase_Newtype : ResolvedTypeBase {
    public readonly DAST._IType _baseType;
    public readonly DAST._INewtypeRange _range;
    public readonly bool _erase;
    public ResolvedTypeBase_Newtype(DAST._IType baseType, DAST._INewtypeRange range, bool erase) : base() {
      this._baseType = baseType;
      this._range = range;
      this._erase = erase;
    }
    public override _IResolvedTypeBase DowncastClone() {
      if (this is _IResolvedTypeBase dt) { return dt; }
      return new ResolvedTypeBase_Newtype(_baseType, _range, _erase);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ResolvedTypeBase_Newtype;
      return oth != null && object.Equals(this._baseType, oth._baseType) && object.Equals(this._range, oth._range) && this._erase == oth._erase;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._baseType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._range));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._erase));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.ResolvedTypeBase.Newtype";
      s += "(";
      s += Dafny.Helpers.ToString(this._baseType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._range);
      s += ", ";
      s += Dafny.Helpers.ToString(this._erase);
      s += ")";
      return s;
    }
  }

  public interface _IResolvedType {
    bool is_ResolvedType { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_path { get; }
    Dafny.ISequence<DAST._IType> dtor_typeArgs { get; }
    DAST._IResolvedTypeBase dtor_kind { get; }
    Dafny.ISequence<DAST._IAttribute> dtor_attributes { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_properMethods { get; }
    Dafny.ISequence<DAST._IType> dtor_extendedTypes { get; }
    _IResolvedType DowncastClone();
    DAST._IResolvedType Replace(Dafny.IMap<DAST._IType,DAST._IType> mapping);
  }
  public class ResolvedType : _IResolvedType {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _path;
    public readonly Dafny.ISequence<DAST._IType> _typeArgs;
    public readonly DAST._IResolvedTypeBase _kind;
    public readonly Dafny.ISequence<DAST._IAttribute> _attributes;
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _properMethods;
    public readonly Dafny.ISequence<DAST._IType> _extendedTypes;
    public ResolvedType(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path, Dafny.ISequence<DAST._IType> typeArgs, DAST._IResolvedTypeBase kind, Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> properMethods, Dafny.ISequence<DAST._IType> extendedTypes) {
      this._path = path;
      this._typeArgs = typeArgs;
      this._kind = kind;
      this._attributes = attributes;
      this._properMethods = properMethods;
      this._extendedTypes = extendedTypes;
    }
    public _IResolvedType DowncastClone() {
      if (this is _IResolvedType dt) { return dt; }
      return new ResolvedType(_path, _typeArgs, _kind, _attributes, _properMethods, _extendedTypes);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ResolvedType;
      return oth != null && object.Equals(this._path, oth._path) && object.Equals(this._typeArgs, oth._typeArgs) && object.Equals(this._kind, oth._kind) && object.Equals(this._attributes, oth._attributes) && object.Equals(this._properMethods, oth._properMethods) && object.Equals(this._extendedTypes, oth._extendedTypes);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._path));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeArgs));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._kind));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._properMethods));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._extendedTypes));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.ResolvedType.ResolvedType";
      s += "(";
      s += Dafny.Helpers.ToString(this._path);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeArgs);
      s += ", ";
      s += Dafny.Helpers.ToString(this._kind);
      s += ", ";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ", ";
      s += Dafny.Helpers.ToString(this._properMethods);
      s += ", ";
      s += Dafny.Helpers.ToString(this._extendedTypes);
      s += ")";
      return s;
    }
    private static readonly DAST._IResolvedType theDefault = create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Empty, Dafny.Sequence<DAST._IType>.Empty, DAST.ResolvedTypeBase.Default(), Dafny.Sequence<DAST._IAttribute>.Empty, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Empty, Dafny.Sequence<DAST._IType>.Empty);
    public static DAST._IResolvedType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IResolvedType> _TYPE = new Dafny.TypeDescriptor<DAST._IResolvedType>(DAST.ResolvedType.Default());
    public static Dafny.TypeDescriptor<DAST._IResolvedType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IResolvedType create(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path, Dafny.ISequence<DAST._IType> typeArgs, DAST._IResolvedTypeBase kind, Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> properMethods, Dafny.ISequence<DAST._IType> extendedTypes) {
      return new ResolvedType(path, typeArgs, kind, attributes, properMethods, extendedTypes);
    }
    public static _IResolvedType create_ResolvedType(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path, Dafny.ISequence<DAST._IType> typeArgs, DAST._IResolvedTypeBase kind, Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> properMethods, Dafny.ISequence<DAST._IType> extendedTypes) {
      return create(path, typeArgs, kind, attributes, properMethods, extendedTypes);
    }
    public bool is_ResolvedType { get { return true; } }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_path {
      get {
        return this._path;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_typeArgs {
      get {
        return this._typeArgs;
      }
    }
    public DAST._IResolvedTypeBase dtor_kind {
      get {
        return this._kind;
      }
    }
    public Dafny.ISequence<DAST._IAttribute> dtor_attributes {
      get {
        return this._attributes;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_properMethods {
      get {
        return this._properMethods;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_extendedTypes {
      get {
        return this._extendedTypes;
      }
    }
    public DAST._IResolvedType Replace(Dafny.IMap<DAST._IType,DAST._IType> mapping) {
      return DAST.ResolvedType.create((this).dtor_path, Std.Collections.Seq.__default.Map<DAST._IType, DAST._IType>(Dafny.Helpers.Id<Func<Dafny.IMap<DAST._IType,DAST._IType>, Func<DAST._IType, DAST._IType>>>((_0_mapping) => ((System.Func<DAST._IType, DAST._IType>)((_1_t) => {
  return (_1_t).Replace(_0_mapping);
})))(mapping), (this).dtor_typeArgs), ((System.Func<DAST._IResolvedTypeBase>)(() => {
  DAST._IResolvedTypeBase _source0 = (this).dtor_kind;
  {
    if (_source0.is_Newtype) {
      DAST._IType _2_baseType = _source0.dtor_baseType;
      DAST._INewtypeRange _3_range = _source0.dtor_range;
      bool _4_erase = _source0.dtor_erase;
      return DAST.ResolvedTypeBase.create_Newtype((_2_baseType).Replace(mapping), _3_range, _4_erase);
    }
  }
  {
    return (this).dtor_kind;
  }
}))(), (this).dtor_attributes, (this).dtor_properMethods, Std.Collections.Seq.__default.Map<DAST._IType, DAST._IType>(Dafny.Helpers.Id<Func<Dafny.IMap<DAST._IType,DAST._IType>, Func<DAST._IType, DAST._IType>>>((_5_mapping) => ((System.Func<DAST._IType, DAST._IType>)((_6_t) => {
  return (_6_t).Replace(_5_mapping);
})))(mapping), (this).dtor_extendedTypes));
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
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Ident.Ident";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
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
    Dafny.ISequence<Dafny.Rune> dtor_docString { get; }
    Dafny.ISequence<Dafny.Rune> dtor_enclosingModule { get; }
    Dafny.ISequence<DAST._ITypeArgDecl> dtor_typeParams { get; }
    Dafny.ISequence<DAST._IType> dtor_superTraitTypes { get; }
    Dafny.ISequence<DAST._IField> dtor_fields { get; }
    Dafny.ISequence<DAST._IMethod> dtor_body { get; }
    Dafny.ISequence<DAST._IAttribute> dtor_attributes { get; }
    _IClass DowncastClone();
  }
  public class Class : _IClass {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<Dafny.Rune> _docString;
    public readonly Dafny.ISequence<Dafny.Rune> _enclosingModule;
    public readonly Dafny.ISequence<DAST._ITypeArgDecl> _typeParams;
    public readonly Dafny.ISequence<DAST._IType> _superTraitTypes;
    public readonly Dafny.ISequence<DAST._IField> _fields;
    public readonly Dafny.ISequence<DAST._IMethod> _body;
    public readonly Dafny.ISequence<DAST._IAttribute> _attributes;
    public Class(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<DAST._ITypeArgDecl> typeParams, Dafny.ISequence<DAST._IType> superTraitTypes, Dafny.ISequence<DAST._IField> fields, Dafny.ISequence<DAST._IMethod> body, Dafny.ISequence<DAST._IAttribute> attributes) {
      this._name = name;
      this._docString = docString;
      this._enclosingModule = enclosingModule;
      this._typeParams = typeParams;
      this._superTraitTypes = superTraitTypes;
      this._fields = fields;
      this._body = body;
      this._attributes = attributes;
    }
    public _IClass DowncastClone() {
      if (this is _IClass dt) { return dt; }
      return new Class(_name, _docString, _enclosingModule, _typeParams, _superTraitTypes, _fields, _body, _attributes);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Class;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._docString, oth._docString) && object.Equals(this._enclosingModule, oth._enclosingModule) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._superTraitTypes, oth._superTraitTypes) && object.Equals(this._fields, oth._fields) && object.Equals(this._body, oth._body) && object.Equals(this._attributes, oth._attributes);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docString));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._enclosingModule));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._superTraitTypes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fields));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Class.Class";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += this._docString.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._enclosingModule);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._superTraitTypes);
      s += ", ";
      s += Dafny.Helpers.ToString(this._fields);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ", ";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ")";
      return s;
    }
    private static readonly DAST._IClass theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._ITypeArgDecl>.Empty, Dafny.Sequence<DAST._IType>.Empty, Dafny.Sequence<DAST._IField>.Empty, Dafny.Sequence<DAST._IMethod>.Empty, Dafny.Sequence<DAST._IAttribute>.Empty);
    public static DAST._IClass Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IClass> _TYPE = new Dafny.TypeDescriptor<DAST._IClass>(DAST.Class.Default());
    public static Dafny.TypeDescriptor<DAST._IClass> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IClass create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<DAST._ITypeArgDecl> typeParams, Dafny.ISequence<DAST._IType> superTraitTypes, Dafny.ISequence<DAST._IField> fields, Dafny.ISequence<DAST._IMethod> body, Dafny.ISequence<DAST._IAttribute> attributes) {
      return new Class(name, docString, enclosingModule, typeParams, superTraitTypes, fields, body, attributes);
    }
    public static _IClass create_Class(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<DAST._ITypeArgDecl> typeParams, Dafny.ISequence<DAST._IType> superTraitTypes, Dafny.ISequence<DAST._IField> fields, Dafny.ISequence<DAST._IMethod> body, Dafny.ISequence<DAST._IAttribute> attributes) {
      return create(name, docString, enclosingModule, typeParams, superTraitTypes, fields, body, attributes);
    }
    public bool is_Class { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_docString {
      get {
        return this._docString;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_enclosingModule {
      get {
        return this._enclosingModule;
      }
    }
    public Dafny.ISequence<DAST._ITypeArgDecl> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_superTraitTypes {
      get {
        return this._superTraitTypes;
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
    public Dafny.ISequence<DAST._IAttribute> dtor_attributes {
      get {
        return this._attributes;
      }
    }
  }

  public interface _ITrait {
    bool is_Trait { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<Dafny.Rune> dtor_docString { get; }
    Dafny.ISequence<DAST._ITypeArgDecl> dtor_typeParams { get; }
    DAST._ITraitType dtor_traitType { get; }
    Dafny.ISequence<DAST._IType> dtor_parents { get; }
    Dafny.ISequence<DAST._IType> dtor_downcastableTraits { get; }
    Dafny.ISequence<DAST._IMethod> dtor_body { get; }
    Dafny.ISequence<DAST._IAttribute> dtor_attributes { get; }
    _ITrait DowncastClone();
  }
  public class Trait : _ITrait {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<Dafny.Rune> _docString;
    public readonly Dafny.ISequence<DAST._ITypeArgDecl> _typeParams;
    public readonly DAST._ITraitType _traitType;
    public readonly Dafny.ISequence<DAST._IType> _parents;
    public readonly Dafny.ISequence<DAST._IType> _downcastableTraits;
    public readonly Dafny.ISequence<DAST._IMethod> _body;
    public readonly Dafny.ISequence<DAST._IAttribute> _attributes;
    public Trait(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<DAST._ITypeArgDecl> typeParams, DAST._ITraitType traitType, Dafny.ISequence<DAST._IType> parents, Dafny.ISequence<DAST._IType> downcastableTraits, Dafny.ISequence<DAST._IMethod> body, Dafny.ISequence<DAST._IAttribute> attributes) {
      this._name = name;
      this._docString = docString;
      this._typeParams = typeParams;
      this._traitType = traitType;
      this._parents = parents;
      this._downcastableTraits = downcastableTraits;
      this._body = body;
      this._attributes = attributes;
    }
    public _ITrait DowncastClone() {
      if (this is _ITrait dt) { return dt; }
      return new Trait(_name, _docString, _typeParams, _traitType, _parents, _downcastableTraits, _body, _attributes);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Trait;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._docString, oth._docString) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._traitType, oth._traitType) && object.Equals(this._parents, oth._parents) && object.Equals(this._downcastableTraits, oth._downcastableTraits) && object.Equals(this._body, oth._body) && object.Equals(this._attributes, oth._attributes);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docString));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._traitType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._parents));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._downcastableTraits));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Trait.Trait";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += this._docString.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._traitType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._parents);
      s += ", ";
      s += Dafny.Helpers.ToString(this._downcastableTraits);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ", ";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ")";
      return s;
    }
    private static readonly DAST._ITrait theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._ITypeArgDecl>.Empty, DAST.TraitType.Default(), Dafny.Sequence<DAST._IType>.Empty, Dafny.Sequence<DAST._IType>.Empty, Dafny.Sequence<DAST._IMethod>.Empty, Dafny.Sequence<DAST._IAttribute>.Empty);
    public static DAST._ITrait Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._ITrait> _TYPE = new Dafny.TypeDescriptor<DAST._ITrait>(DAST.Trait.Default());
    public static Dafny.TypeDescriptor<DAST._ITrait> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITrait create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<DAST._ITypeArgDecl> typeParams, DAST._ITraitType traitType, Dafny.ISequence<DAST._IType> parents, Dafny.ISequence<DAST._IType> downcastableTraits, Dafny.ISequence<DAST._IMethod> body, Dafny.ISequence<DAST._IAttribute> attributes) {
      return new Trait(name, docString, typeParams, traitType, parents, downcastableTraits, body, attributes);
    }
    public static _ITrait create_Trait(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<DAST._ITypeArgDecl> typeParams, DAST._ITraitType traitType, Dafny.ISequence<DAST._IType> parents, Dafny.ISequence<DAST._IType> downcastableTraits, Dafny.ISequence<DAST._IMethod> body, Dafny.ISequence<DAST._IAttribute> attributes) {
      return create(name, docString, typeParams, traitType, parents, downcastableTraits, body, attributes);
    }
    public bool is_Trait { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_docString {
      get {
        return this._docString;
      }
    }
    public Dafny.ISequence<DAST._ITypeArgDecl> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public DAST._ITraitType dtor_traitType {
      get {
        return this._traitType;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_parents {
      get {
        return this._parents;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_downcastableTraits {
      get {
        return this._downcastableTraits;
      }
    }
    public Dafny.ISequence<DAST._IMethod> dtor_body {
      get {
        return this._body;
      }
    }
    public Dafny.ISequence<DAST._IAttribute> dtor_attributes {
      get {
        return this._attributes;
      }
    }
  }

  public interface _IDatatype {
    bool is_Datatype { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<Dafny.Rune> dtor_docString { get; }
    Dafny.ISequence<Dafny.Rune> dtor_enclosingModule { get; }
    Dafny.ISequence<DAST._ITypeArgDecl> dtor_typeParams { get; }
    Dafny.ISequence<DAST._IDatatypeCtor> dtor_ctors { get; }
    Dafny.ISequence<DAST._IMethod> dtor_body { get; }
    bool dtor_isCo { get; }
    DAST._IEqualitySupport dtor_equalitySupport { get; }
    Dafny.ISequence<DAST._IAttribute> dtor_attributes { get; }
    Dafny.ISequence<DAST._IType> dtor_superTraitTypes { get; }
    Dafny.ISequence<DAST._IType> dtor_superTraitNegativeTypes { get; }
    _IDatatype DowncastClone();
  }
  public class Datatype : _IDatatype {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<Dafny.Rune> _docString;
    public readonly Dafny.ISequence<Dafny.Rune> _enclosingModule;
    public readonly Dafny.ISequence<DAST._ITypeArgDecl> _typeParams;
    public readonly Dafny.ISequence<DAST._IDatatypeCtor> _ctors;
    public readonly Dafny.ISequence<DAST._IMethod> _body;
    public readonly bool _isCo;
    public readonly DAST._IEqualitySupport _equalitySupport;
    public readonly Dafny.ISequence<DAST._IAttribute> _attributes;
    public readonly Dafny.ISequence<DAST._IType> _superTraitTypes;
    public readonly Dafny.ISequence<DAST._IType> _superTraitNegativeTypes;
    public Datatype(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<DAST._ITypeArgDecl> typeParams, Dafny.ISequence<DAST._IDatatypeCtor> ctors, Dafny.ISequence<DAST._IMethod> body, bool isCo, DAST._IEqualitySupport equalitySupport, Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<DAST._IType> superTraitTypes, Dafny.ISequence<DAST._IType> superTraitNegativeTypes) {
      this._name = name;
      this._docString = docString;
      this._enclosingModule = enclosingModule;
      this._typeParams = typeParams;
      this._ctors = ctors;
      this._body = body;
      this._isCo = isCo;
      this._equalitySupport = equalitySupport;
      this._attributes = attributes;
      this._superTraitTypes = superTraitTypes;
      this._superTraitNegativeTypes = superTraitNegativeTypes;
    }
    public _IDatatype DowncastClone() {
      if (this is _IDatatype dt) { return dt; }
      return new Datatype(_name, _docString, _enclosingModule, _typeParams, _ctors, _body, _isCo, _equalitySupport, _attributes, _superTraitTypes, _superTraitNegativeTypes);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Datatype;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._docString, oth._docString) && object.Equals(this._enclosingModule, oth._enclosingModule) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._ctors, oth._ctors) && object.Equals(this._body, oth._body) && this._isCo == oth._isCo && object.Equals(this._equalitySupport, oth._equalitySupport) && object.Equals(this._attributes, oth._attributes) && object.Equals(this._superTraitTypes, oth._superTraitTypes) && object.Equals(this._superTraitNegativeTypes, oth._superTraitNegativeTypes);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docString));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._enclosingModule));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ctors));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._isCo));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._equalitySupport));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._superTraitTypes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._superTraitNegativeTypes));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Datatype.Datatype";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += this._docString.ToVerbatimString(true);
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
      s += ", ";
      s += Dafny.Helpers.ToString(this._equalitySupport);
      s += ", ";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ", ";
      s += Dafny.Helpers.ToString(this._superTraitTypes);
      s += ", ";
      s += Dafny.Helpers.ToString(this._superTraitNegativeTypes);
      s += ")";
      return s;
    }
    private static readonly DAST._IDatatype theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._ITypeArgDecl>.Empty, Dafny.Sequence<DAST._IDatatypeCtor>.Empty, Dafny.Sequence<DAST._IMethod>.Empty, false, DAST.EqualitySupport.Default(), Dafny.Sequence<DAST._IAttribute>.Empty, Dafny.Sequence<DAST._IType>.Empty, Dafny.Sequence<DAST._IType>.Empty);
    public static DAST._IDatatype Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IDatatype> _TYPE = new Dafny.TypeDescriptor<DAST._IDatatype>(DAST.Datatype.Default());
    public static Dafny.TypeDescriptor<DAST._IDatatype> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDatatype create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<DAST._ITypeArgDecl> typeParams, Dafny.ISequence<DAST._IDatatypeCtor> ctors, Dafny.ISequence<DAST._IMethod> body, bool isCo, DAST._IEqualitySupport equalitySupport, Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<DAST._IType> superTraitTypes, Dafny.ISequence<DAST._IType> superTraitNegativeTypes) {
      return new Datatype(name, docString, enclosingModule, typeParams, ctors, body, isCo, equalitySupport, attributes, superTraitTypes, superTraitNegativeTypes);
    }
    public static _IDatatype create_Datatype(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<DAST._ITypeArgDecl> typeParams, Dafny.ISequence<DAST._IDatatypeCtor> ctors, Dafny.ISequence<DAST._IMethod> body, bool isCo, DAST._IEqualitySupport equalitySupport, Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<DAST._IType> superTraitTypes, Dafny.ISequence<DAST._IType> superTraitNegativeTypes) {
      return create(name, docString, enclosingModule, typeParams, ctors, body, isCo, equalitySupport, attributes, superTraitTypes, superTraitNegativeTypes);
    }
    public bool is_Datatype { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_docString {
      get {
        return this._docString;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_enclosingModule {
      get {
        return this._enclosingModule;
      }
    }
    public Dafny.ISequence<DAST._ITypeArgDecl> dtor_typeParams {
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
    public DAST._IEqualitySupport dtor_equalitySupport {
      get {
        return this._equalitySupport;
      }
    }
    public Dafny.ISequence<DAST._IAttribute> dtor_attributes {
      get {
        return this._attributes;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_superTraitTypes {
      get {
        return this._superTraitTypes;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_superTraitNegativeTypes {
      get {
        return this._superTraitNegativeTypes;
      }
    }
  }

  public interface _IDatatypeDtor {
    bool is_DatatypeDtor { get; }
    DAST._IFormal dtor_formal { get; }
    Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> dtor_callName { get; }
    _IDatatypeDtor DowncastClone();
  }
  public class DatatypeDtor : _IDatatypeDtor {
    public readonly DAST._IFormal _formal;
    public readonly Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _callName;
    public DatatypeDtor(DAST._IFormal formal, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> callName) {
      this._formal = formal;
      this._callName = callName;
    }
    public _IDatatypeDtor DowncastClone() {
      if (this is _IDatatypeDtor dt) { return dt; }
      return new DatatypeDtor(_formal, _callName);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.DatatypeDtor;
      return oth != null && object.Equals(this._formal, oth._formal) && object.Equals(this._callName, oth._callName);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._formal));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._callName));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.DatatypeDtor.DatatypeDtor";
      s += "(";
      s += Dafny.Helpers.ToString(this._formal);
      s += ", ";
      s += Dafny.Helpers.ToString(this._callName);
      s += ")";
      return s;
    }
    private static readonly DAST._IDatatypeDtor theDefault = create(DAST.Formal.Default(), Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.Default());
    public static DAST._IDatatypeDtor Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IDatatypeDtor> _TYPE = new Dafny.TypeDescriptor<DAST._IDatatypeDtor>(DAST.DatatypeDtor.Default());
    public static Dafny.TypeDescriptor<DAST._IDatatypeDtor> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDatatypeDtor create(DAST._IFormal formal, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> callName) {
      return new DatatypeDtor(formal, callName);
    }
    public static _IDatatypeDtor create_DatatypeDtor(DAST._IFormal formal, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> callName) {
      return create(formal, callName);
    }
    public bool is_DatatypeDtor { get { return true; } }
    public DAST._IFormal dtor_formal {
      get {
        return this._formal;
      }
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> dtor_callName {
      get {
        return this._callName;
      }
    }
  }

  public interface _IDatatypeCtor {
    bool is_DatatypeCtor { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<Dafny.Rune> dtor_docString { get; }
    Dafny.ISequence<DAST._IDatatypeDtor> dtor_args { get; }
    bool dtor_hasAnyArgs { get; }
    _IDatatypeCtor DowncastClone();
  }
  public class DatatypeCtor : _IDatatypeCtor {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<Dafny.Rune> _docString;
    public readonly Dafny.ISequence<DAST._IDatatypeDtor> _args;
    public readonly bool _hasAnyArgs;
    public DatatypeCtor(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<DAST._IDatatypeDtor> args, bool hasAnyArgs) {
      this._name = name;
      this._docString = docString;
      this._args = args;
      this._hasAnyArgs = hasAnyArgs;
    }
    public _IDatatypeCtor DowncastClone() {
      if (this is _IDatatypeCtor dt) { return dt; }
      return new DatatypeCtor(_name, _docString, _args, _hasAnyArgs);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.DatatypeCtor;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._docString, oth._docString) && object.Equals(this._args, oth._args) && this._hasAnyArgs == oth._hasAnyArgs;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docString));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._args));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._hasAnyArgs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.DatatypeCtor.DatatypeCtor";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += this._docString.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._args);
      s += ", ";
      s += Dafny.Helpers.ToString(this._hasAnyArgs);
      s += ")";
      return s;
    }
    private static readonly DAST._IDatatypeCtor theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._IDatatypeDtor>.Empty, false);
    public static DAST._IDatatypeCtor Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IDatatypeCtor> _TYPE = new Dafny.TypeDescriptor<DAST._IDatatypeCtor>(DAST.DatatypeCtor.Default());
    public static Dafny.TypeDescriptor<DAST._IDatatypeCtor> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDatatypeCtor create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<DAST._IDatatypeDtor> args, bool hasAnyArgs) {
      return new DatatypeCtor(name, docString, args, hasAnyArgs);
    }
    public static _IDatatypeCtor create_DatatypeCtor(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<DAST._IDatatypeDtor> args, bool hasAnyArgs) {
      return create(name, docString, args, hasAnyArgs);
    }
    public bool is_DatatypeCtor { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_docString {
      get {
        return this._docString;
      }
    }
    public Dafny.ISequence<DAST._IDatatypeDtor> dtor_args {
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
    Dafny.ISequence<Dafny.Rune> dtor_docString { get; }
    Dafny.ISequence<DAST._ITypeArgDecl> dtor_typeParams { get; }
    DAST._IType dtor_base { get; }
    DAST._INewtypeRange dtor_range { get; }
    Std.Wrappers._IOption<DAST._INewtypeConstraint> dtor_constraint { get; }
    Dafny.ISequence<DAST._IStatement> dtor_witnessStmts { get; }
    Std.Wrappers._IOption<DAST._IExpression> dtor_witnessExpr { get; }
    DAST._IEqualitySupport dtor_equalitySupport { get; }
    Dafny.ISequence<DAST._IAttribute> dtor_attributes { get; }
    Dafny.ISequence<DAST._IMethod> dtor_classItems { get; }
    _INewtype DowncastClone();
  }
  public class Newtype : _INewtype {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<Dafny.Rune> _docString;
    public readonly Dafny.ISequence<DAST._ITypeArgDecl> _typeParams;
    public readonly DAST._IType _base;
    public readonly DAST._INewtypeRange _range;
    public readonly Std.Wrappers._IOption<DAST._INewtypeConstraint> _constraint;
    public readonly Dafny.ISequence<DAST._IStatement> _witnessStmts;
    public readonly Std.Wrappers._IOption<DAST._IExpression> _witnessExpr;
    public readonly DAST._IEqualitySupport _equalitySupport;
    public readonly Dafny.ISequence<DAST._IAttribute> _attributes;
    public readonly Dafny.ISequence<DAST._IMethod> _classItems;
    public Newtype(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<DAST._ITypeArgDecl> typeParams, DAST._IType @base, DAST._INewtypeRange range, Std.Wrappers._IOption<DAST._INewtypeConstraint> constraint, Dafny.ISequence<DAST._IStatement> witnessStmts, Std.Wrappers._IOption<DAST._IExpression> witnessExpr, DAST._IEqualitySupport equalitySupport, Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<DAST._IMethod> classItems) {
      this._name = name;
      this._docString = docString;
      this._typeParams = typeParams;
      this._base = @base;
      this._range = range;
      this._constraint = constraint;
      this._witnessStmts = witnessStmts;
      this._witnessExpr = witnessExpr;
      this._equalitySupport = equalitySupport;
      this._attributes = attributes;
      this._classItems = classItems;
    }
    public _INewtype DowncastClone() {
      if (this is _INewtype dt) { return dt; }
      return new Newtype(_name, _docString, _typeParams, _base, _range, _constraint, _witnessStmts, _witnessExpr, _equalitySupport, _attributes, _classItems);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Newtype;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._docString, oth._docString) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._base, oth._base) && object.Equals(this._range, oth._range) && object.Equals(this._constraint, oth._constraint) && object.Equals(this._witnessStmts, oth._witnessStmts) && object.Equals(this._witnessExpr, oth._witnessExpr) && object.Equals(this._equalitySupport, oth._equalitySupport) && object.Equals(this._attributes, oth._attributes) && object.Equals(this._classItems, oth._classItems);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docString));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._base));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._range));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._constraint));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._witnessStmts));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._witnessExpr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._equalitySupport));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._classItems));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Newtype.Newtype";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += this._docString.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._base);
      s += ", ";
      s += Dafny.Helpers.ToString(this._range);
      s += ", ";
      s += Dafny.Helpers.ToString(this._constraint);
      s += ", ";
      s += Dafny.Helpers.ToString(this._witnessStmts);
      s += ", ";
      s += Dafny.Helpers.ToString(this._witnessExpr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._equalitySupport);
      s += ", ";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ", ";
      s += Dafny.Helpers.ToString(this._classItems);
      s += ")";
      return s;
    }
    private static readonly DAST._INewtype theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._ITypeArgDecl>.Empty, DAST.Type.Default(), DAST.NewtypeRange.Default(), Std.Wrappers.Option<DAST._INewtypeConstraint>.Default(), Dafny.Sequence<DAST._IStatement>.Empty, Std.Wrappers.Option<DAST._IExpression>.Default(), DAST.EqualitySupport.Default(), Dafny.Sequence<DAST._IAttribute>.Empty, Dafny.Sequence<DAST._IMethod>.Empty);
    public static DAST._INewtype Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._INewtype> _TYPE = new Dafny.TypeDescriptor<DAST._INewtype>(DAST.Newtype.Default());
    public static Dafny.TypeDescriptor<DAST._INewtype> _TypeDescriptor() {
      return _TYPE;
    }
    public static _INewtype create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<DAST._ITypeArgDecl> typeParams, DAST._IType @base, DAST._INewtypeRange range, Std.Wrappers._IOption<DAST._INewtypeConstraint> constraint, Dafny.ISequence<DAST._IStatement> witnessStmts, Std.Wrappers._IOption<DAST._IExpression> witnessExpr, DAST._IEqualitySupport equalitySupport, Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<DAST._IMethod> classItems) {
      return new Newtype(name, docString, typeParams, @base, range, constraint, witnessStmts, witnessExpr, equalitySupport, attributes, classItems);
    }
    public static _INewtype create_Newtype(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<DAST._ITypeArgDecl> typeParams, DAST._IType @base, DAST._INewtypeRange range, Std.Wrappers._IOption<DAST._INewtypeConstraint> constraint, Dafny.ISequence<DAST._IStatement> witnessStmts, Std.Wrappers._IOption<DAST._IExpression> witnessExpr, DAST._IEqualitySupport equalitySupport, Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<DAST._IMethod> classItems) {
      return create(name, docString, typeParams, @base, range, constraint, witnessStmts, witnessExpr, equalitySupport, attributes, classItems);
    }
    public bool is_Newtype { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_docString {
      get {
        return this._docString;
      }
    }
    public Dafny.ISequence<DAST._ITypeArgDecl> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public DAST._IType dtor_base {
      get {
        return this._base;
      }
    }
    public DAST._INewtypeRange dtor_range {
      get {
        return this._range;
      }
    }
    public Std.Wrappers._IOption<DAST._INewtypeConstraint> dtor_constraint {
      get {
        return this._constraint;
      }
    }
    public Dafny.ISequence<DAST._IStatement> dtor_witnessStmts {
      get {
        return this._witnessStmts;
      }
    }
    public Std.Wrappers._IOption<DAST._IExpression> dtor_witnessExpr {
      get {
        return this._witnessExpr;
      }
    }
    public DAST._IEqualitySupport dtor_equalitySupport {
      get {
        return this._equalitySupport;
      }
    }
    public Dafny.ISequence<DAST._IAttribute> dtor_attributes {
      get {
        return this._attributes;
      }
    }
    public Dafny.ISequence<DAST._IMethod> dtor_classItems {
      get {
        return this._classItems;
      }
    }
  }

  public interface _INewtypeConstraint {
    bool is_NewtypeConstraint { get; }
    DAST._IFormal dtor_variable { get; }
    Dafny.ISequence<DAST._IStatement> dtor_constraintStmts { get; }
    _INewtypeConstraint DowncastClone();
  }
  public class NewtypeConstraint : _INewtypeConstraint {
    public readonly DAST._IFormal _variable;
    public readonly Dafny.ISequence<DAST._IStatement> _constraintStmts;
    public NewtypeConstraint(DAST._IFormal variable, Dafny.ISequence<DAST._IStatement> constraintStmts) {
      this._variable = variable;
      this._constraintStmts = constraintStmts;
    }
    public _INewtypeConstraint DowncastClone() {
      if (this is _INewtypeConstraint dt) { return dt; }
      return new NewtypeConstraint(_variable, _constraintStmts);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeConstraint;
      return oth != null && object.Equals(this._variable, oth._variable) && object.Equals(this._constraintStmts, oth._constraintStmts);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._variable));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._constraintStmts));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeConstraint.NewtypeConstraint";
      s += "(";
      s += Dafny.Helpers.ToString(this._variable);
      s += ", ";
      s += Dafny.Helpers.ToString(this._constraintStmts);
      s += ")";
      return s;
    }
    private static readonly DAST._INewtypeConstraint theDefault = create(DAST.Formal.Default(), Dafny.Sequence<DAST._IStatement>.Empty);
    public static DAST._INewtypeConstraint Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._INewtypeConstraint> _TYPE = new Dafny.TypeDescriptor<DAST._INewtypeConstraint>(DAST.NewtypeConstraint.Default());
    public static Dafny.TypeDescriptor<DAST._INewtypeConstraint> _TypeDescriptor() {
      return _TYPE;
    }
    public static _INewtypeConstraint create(DAST._IFormal variable, Dafny.ISequence<DAST._IStatement> constraintStmts) {
      return new NewtypeConstraint(variable, constraintStmts);
    }
    public static _INewtypeConstraint create_NewtypeConstraint(DAST._IFormal variable, Dafny.ISequence<DAST._IStatement> constraintStmts) {
      return create(variable, constraintStmts);
    }
    public bool is_NewtypeConstraint { get { return true; } }
    public DAST._IFormal dtor_variable {
      get {
        return this._variable;
      }
    }
    public Dafny.ISequence<DAST._IStatement> dtor_constraintStmts {
      get {
        return this._constraintStmts;
      }
    }
  }

  public interface _ISynonymType {
    bool is_SynonymType { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<Dafny.Rune> dtor_docString { get; }
    Dafny.ISequence<DAST._ITypeArgDecl> dtor_typeParams { get; }
    DAST._IType dtor_base { get; }
    Dafny.ISequence<DAST._IStatement> dtor_witnessStmts { get; }
    Std.Wrappers._IOption<DAST._IExpression> dtor_witnessExpr { get; }
    Dafny.ISequence<DAST._IAttribute> dtor_attributes { get; }
    _ISynonymType DowncastClone();
  }
  public class SynonymType : _ISynonymType {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<Dafny.Rune> _docString;
    public readonly Dafny.ISequence<DAST._ITypeArgDecl> _typeParams;
    public readonly DAST._IType _base;
    public readonly Dafny.ISequence<DAST._IStatement> _witnessStmts;
    public readonly Std.Wrappers._IOption<DAST._IExpression> _witnessExpr;
    public readonly Dafny.ISequence<DAST._IAttribute> _attributes;
    public SynonymType(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<DAST._ITypeArgDecl> typeParams, DAST._IType @base, Dafny.ISequence<DAST._IStatement> witnessStmts, Std.Wrappers._IOption<DAST._IExpression> witnessExpr, Dafny.ISequence<DAST._IAttribute> attributes) {
      this._name = name;
      this._docString = docString;
      this._typeParams = typeParams;
      this._base = @base;
      this._witnessStmts = witnessStmts;
      this._witnessExpr = witnessExpr;
      this._attributes = attributes;
    }
    public _ISynonymType DowncastClone() {
      if (this is _ISynonymType dt) { return dt; }
      return new SynonymType(_name, _docString, _typeParams, _base, _witnessStmts, _witnessExpr, _attributes);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.SynonymType;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._docString, oth._docString) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._base, oth._base) && object.Equals(this._witnessStmts, oth._witnessStmts) && object.Equals(this._witnessExpr, oth._witnessExpr) && object.Equals(this._attributes, oth._attributes);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docString));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._base));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._witnessStmts));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._witnessExpr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.SynonymType.SynonymType";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += this._docString.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._base);
      s += ", ";
      s += Dafny.Helpers.ToString(this._witnessStmts);
      s += ", ";
      s += Dafny.Helpers.ToString(this._witnessExpr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ")";
      return s;
    }
    private static readonly DAST._ISynonymType theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._ITypeArgDecl>.Empty, DAST.Type.Default(), Dafny.Sequence<DAST._IStatement>.Empty, Std.Wrappers.Option<DAST._IExpression>.Default(), Dafny.Sequence<DAST._IAttribute>.Empty);
    public static DAST._ISynonymType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._ISynonymType> _TYPE = new Dafny.TypeDescriptor<DAST._ISynonymType>(DAST.SynonymType.Default());
    public static Dafny.TypeDescriptor<DAST._ISynonymType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISynonymType create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<DAST._ITypeArgDecl> typeParams, DAST._IType @base, Dafny.ISequence<DAST._IStatement> witnessStmts, Std.Wrappers._IOption<DAST._IExpression> witnessExpr, Dafny.ISequence<DAST._IAttribute> attributes) {
      return new SynonymType(name, docString, typeParams, @base, witnessStmts, witnessExpr, attributes);
    }
    public static _ISynonymType create_SynonymType(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<DAST._ITypeArgDecl> typeParams, DAST._IType @base, Dafny.ISequence<DAST._IStatement> witnessStmts, Std.Wrappers._IOption<DAST._IExpression> witnessExpr, Dafny.ISequence<DAST._IAttribute> attributes) {
      return create(name, docString, typeParams, @base, witnessStmts, witnessExpr, attributes);
    }
    public bool is_SynonymType { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_docString {
      get {
        return this._docString;
      }
    }
    public Dafny.ISequence<DAST._ITypeArgDecl> dtor_typeParams {
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
    public Std.Wrappers._IOption<DAST._IExpression> dtor_witnessExpr {
      get {
        return this._witnessExpr;
      }
    }
    public Dafny.ISequence<DAST._IAttribute> dtor_attributes {
      get {
        return this._attributes;
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
      return (int) hash;
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
    bool dtor_isConstant { get; }
    Std.Wrappers._IOption<DAST._IExpression> dtor_defaultValue { get; }
    bool dtor_isStatic { get; }
    _IField DowncastClone();
  }
  public class Field : _IField {
    public readonly DAST._IFormal _formal;
    public readonly bool _isConstant;
    public readonly Std.Wrappers._IOption<DAST._IExpression> _defaultValue;
    public readonly bool _isStatic;
    public Field(DAST._IFormal formal, bool isConstant, Std.Wrappers._IOption<DAST._IExpression> defaultValue, bool isStatic) {
      this._formal = formal;
      this._isConstant = isConstant;
      this._defaultValue = defaultValue;
      this._isStatic = isStatic;
    }
    public _IField DowncastClone() {
      if (this is _IField dt) { return dt; }
      return new Field(_formal, _isConstant, _defaultValue, _isStatic);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Field;
      return oth != null && object.Equals(this._formal, oth._formal) && this._isConstant == oth._isConstant && object.Equals(this._defaultValue, oth._defaultValue) && this._isStatic == oth._isStatic;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._formal));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._isConstant));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._defaultValue));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._isStatic));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Field.Field";
      s += "(";
      s += Dafny.Helpers.ToString(this._formal);
      s += ", ";
      s += Dafny.Helpers.ToString(this._isConstant);
      s += ", ";
      s += Dafny.Helpers.ToString(this._defaultValue);
      s += ", ";
      s += Dafny.Helpers.ToString(this._isStatic);
      s += ")";
      return s;
    }
    private static readonly DAST._IField theDefault = create(DAST.Formal.Default(), false, Std.Wrappers.Option<DAST._IExpression>.Default(), false);
    public static DAST._IField Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IField> _TYPE = new Dafny.TypeDescriptor<DAST._IField>(DAST.Field.Default());
    public static Dafny.TypeDescriptor<DAST._IField> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IField create(DAST._IFormal formal, bool isConstant, Std.Wrappers._IOption<DAST._IExpression> defaultValue, bool isStatic) {
      return new Field(formal, isConstant, defaultValue, isStatic);
    }
    public static _IField create_Field(DAST._IFormal formal, bool isConstant, Std.Wrappers._IOption<DAST._IExpression> defaultValue, bool isStatic) {
      return create(formal, isConstant, defaultValue, isStatic);
    }
    public bool is_Field { get { return true; } }
    public DAST._IFormal dtor_formal {
      get {
        return this._formal;
      }
    }
    public bool dtor_isConstant {
      get {
        return this._isConstant;
      }
    }
    public Std.Wrappers._IOption<DAST._IExpression> dtor_defaultValue {
      get {
        return this._defaultValue;
      }
    }
    public bool dtor_isStatic {
      get {
        return this._isStatic;
      }
    }
  }

  public interface _IFormal {
    bool is_Formal { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    DAST._IType dtor_typ { get; }
    Dafny.ISequence<DAST._IAttribute> dtor_attributes { get; }
    _IFormal DowncastClone();
  }
  public class Formal : _IFormal {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly DAST._IType _typ;
    public readonly Dafny.ISequence<DAST._IAttribute> _attributes;
    public Formal(Dafny.ISequence<Dafny.Rune> name, DAST._IType typ, Dafny.ISequence<DAST._IAttribute> attributes) {
      this._name = name;
      this._typ = typ;
      this._attributes = attributes;
    }
    public _IFormal DowncastClone() {
      if (this is _IFormal dt) { return dt; }
      return new Formal(_name, _typ, _attributes);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Formal;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._typ, oth._typ) && object.Equals(this._attributes, oth._attributes);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typ));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Formal.Formal";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typ);
      s += ", ";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ")";
      return s;
    }
    private static readonly DAST._IFormal theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, DAST.Type.Default(), Dafny.Sequence<DAST._IAttribute>.Empty);
    public static DAST._IFormal Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IFormal> _TYPE = new Dafny.TypeDescriptor<DAST._IFormal>(DAST.Formal.Default());
    public static Dafny.TypeDescriptor<DAST._IFormal> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IFormal create(Dafny.ISequence<Dafny.Rune> name, DAST._IType typ, Dafny.ISequence<DAST._IAttribute> attributes) {
      return new Formal(name, typ, attributes);
    }
    public static _IFormal create_Formal(Dafny.ISequence<Dafny.Rune> name, DAST._IType typ, Dafny.ISequence<DAST._IAttribute> attributes) {
      return create(name, typ, attributes);
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
    public Dafny.ISequence<DAST._IAttribute> dtor_attributes {
      get {
        return this._attributes;
      }
    }
  }

  public interface _IMethod {
    bool is_Method { get; }
    Dafny.ISequence<Dafny.Rune> dtor_docString { get; }
    Dafny.ISequence<DAST._IAttribute> dtor_attributes { get; }
    bool dtor_isStatic { get; }
    bool dtor_hasBody { get; }
    bool dtor_outVarsAreUninitFieldsToAssign { get; }
    bool dtor_wasFunction { get; }
    Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> dtor_overridingPath { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<DAST._ITypeArgDecl> dtor_typeParams { get; }
    Dafny.ISequence<DAST._IFormal> dtor_params { get; }
    Dafny.ISequence<DAST._IFormal> dtor_inheritedParams { get; }
    Dafny.ISequence<DAST._IStatement> dtor_body { get; }
    Dafny.ISequence<DAST._IType> dtor_outTypes { get; }
    Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> dtor_outVars { get; }
    _IMethod DowncastClone();
  }
  public class Method : _IMethod {
    public readonly Dafny.ISequence<Dafny.Rune> _docString;
    public readonly Dafny.ISequence<DAST._IAttribute> _attributes;
    public readonly bool _isStatic;
    public readonly bool _hasBody;
    public readonly bool _outVarsAreUninitFieldsToAssign;
    public readonly bool _wasFunction;
    public readonly Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _overridingPath;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<DAST._ITypeArgDecl> _typeParams;
    public readonly Dafny.ISequence<DAST._IFormal> _params;
    public readonly Dafny.ISequence<DAST._IFormal> _inheritedParams;
    public readonly Dafny.ISequence<DAST._IStatement> _body;
    public readonly Dafny.ISequence<DAST._IType> _outTypes;
    public readonly Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _outVars;
    public Method(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<DAST._IAttribute> attributes, bool isStatic, bool hasBody, bool outVarsAreUninitFieldsToAssign, bool wasFunction, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> overridingPath, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._ITypeArgDecl> typeParams, Dafny.ISequence<DAST._IFormal> @params, Dafny.ISequence<DAST._IFormal> inheritedParams, Dafny.ISequence<DAST._IStatement> body, Dafny.ISequence<DAST._IType> outTypes, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> outVars) {
      this._docString = docString;
      this._attributes = attributes;
      this._isStatic = isStatic;
      this._hasBody = hasBody;
      this._outVarsAreUninitFieldsToAssign = outVarsAreUninitFieldsToAssign;
      this._wasFunction = wasFunction;
      this._overridingPath = overridingPath;
      this._name = name;
      this._typeParams = typeParams;
      this._params = @params;
      this._inheritedParams = inheritedParams;
      this._body = body;
      this._outTypes = outTypes;
      this._outVars = outVars;
    }
    public _IMethod DowncastClone() {
      if (this is _IMethod dt) { return dt; }
      return new Method(_docString, _attributes, _isStatic, _hasBody, _outVarsAreUninitFieldsToAssign, _wasFunction, _overridingPath, _name, _typeParams, _params, _inheritedParams, _body, _outTypes, _outVars);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Method;
      return oth != null && object.Equals(this._docString, oth._docString) && object.Equals(this._attributes, oth._attributes) && this._isStatic == oth._isStatic && this._hasBody == oth._hasBody && this._outVarsAreUninitFieldsToAssign == oth._outVarsAreUninitFieldsToAssign && this._wasFunction == oth._wasFunction && object.Equals(this._overridingPath, oth._overridingPath) && object.Equals(this._name, oth._name) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._params, oth._params) && object.Equals(this._inheritedParams, oth._inheritedParams) && object.Equals(this._body, oth._body) && object.Equals(this._outTypes, oth._outTypes) && object.Equals(this._outVars, oth._outVars);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docString));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._isStatic));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._hasBody));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._outVarsAreUninitFieldsToAssign));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._wasFunction));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overridingPath));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._params));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._inheritedParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._outTypes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._outVars));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Method.Method";
      s += "(";
      s += this._docString.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ", ";
      s += Dafny.Helpers.ToString(this._isStatic);
      s += ", ";
      s += Dafny.Helpers.ToString(this._hasBody);
      s += ", ";
      s += Dafny.Helpers.ToString(this._outVarsAreUninitFieldsToAssign);
      s += ", ";
      s += Dafny.Helpers.ToString(this._wasFunction);
      s += ", ";
      s += Dafny.Helpers.ToString(this._overridingPath);
      s += ", ";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._params);
      s += ", ";
      s += Dafny.Helpers.ToString(this._inheritedParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ", ";
      s += Dafny.Helpers.ToString(this._outTypes);
      s += ", ";
      s += Dafny.Helpers.ToString(this._outVars);
      s += ")";
      return s;
    }
    private static readonly DAST._IMethod theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._IAttribute>.Empty, false, false, false, false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.Default(), Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._ITypeArgDecl>.Empty, Dafny.Sequence<DAST._IFormal>.Empty, Dafny.Sequence<DAST._IFormal>.Empty, Dafny.Sequence<DAST._IStatement>.Empty, Dafny.Sequence<DAST._IType>.Empty, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.Default());
    public static DAST._IMethod Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IMethod> _TYPE = new Dafny.TypeDescriptor<DAST._IMethod>(DAST.Method.Default());
    public static Dafny.TypeDescriptor<DAST._IMethod> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMethod create(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<DAST._IAttribute> attributes, bool isStatic, bool hasBody, bool outVarsAreUninitFieldsToAssign, bool wasFunction, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> overridingPath, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._ITypeArgDecl> typeParams, Dafny.ISequence<DAST._IFormal> @params, Dafny.ISequence<DAST._IFormal> inheritedParams, Dafny.ISequence<DAST._IStatement> body, Dafny.ISequence<DAST._IType> outTypes, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> outVars) {
      return new Method(docString, attributes, isStatic, hasBody, outVarsAreUninitFieldsToAssign, wasFunction, overridingPath, name, typeParams, @params, inheritedParams, body, outTypes, outVars);
    }
    public static _IMethod create_Method(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<DAST._IAttribute> attributes, bool isStatic, bool hasBody, bool outVarsAreUninitFieldsToAssign, bool wasFunction, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> overridingPath, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._ITypeArgDecl> typeParams, Dafny.ISequence<DAST._IFormal> @params, Dafny.ISequence<DAST._IFormal> inheritedParams, Dafny.ISequence<DAST._IStatement> body, Dafny.ISequence<DAST._IType> outTypes, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> outVars) {
      return create(docString, attributes, isStatic, hasBody, outVarsAreUninitFieldsToAssign, wasFunction, overridingPath, name, typeParams, @params, inheritedParams, body, outTypes, outVars);
    }
    public bool is_Method { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_docString {
      get {
        return this._docString;
      }
    }
    public Dafny.ISequence<DAST._IAttribute> dtor_attributes {
      get {
        return this._attributes;
      }
    }
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
    public bool dtor_outVarsAreUninitFieldsToAssign {
      get {
        return this._outVarsAreUninitFieldsToAssign;
      }
    }
    public bool dtor_wasFunction {
      get {
        return this._wasFunction;
      }
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> dtor_overridingPath {
      get {
        return this._overridingPath;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<DAST._ITypeArgDecl> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public Dafny.ISequence<DAST._IFormal> dtor_params {
      get {
        return this._params;
      }
    }
    public Dafny.ISequence<DAST._IFormal> dtor_inheritedParams {
      get {
        return this._inheritedParams;
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
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> dtor_outVars {
      get {
        return this._outVars;
      }
    }
  }

  public interface _ICallSignature {
    bool is_CallSignature { get; }
    Dafny.ISequence<DAST._IFormal> dtor_parameters { get; }
    Dafny.ISequence<DAST._IFormal> dtor_inheritedParams { get; }
    _ICallSignature DowncastClone();
  }
  public class CallSignature : _ICallSignature {
    public readonly Dafny.ISequence<DAST._IFormal> _parameters;
    public readonly Dafny.ISequence<DAST._IFormal> _inheritedParams;
    public CallSignature(Dafny.ISequence<DAST._IFormal> parameters, Dafny.ISequence<DAST._IFormal> inheritedParams) {
      this._parameters = parameters;
      this._inheritedParams = inheritedParams;
    }
    public _ICallSignature DowncastClone() {
      if (this is _ICallSignature dt) { return dt; }
      return new CallSignature(_parameters, _inheritedParams);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.CallSignature;
      return oth != null && object.Equals(this._parameters, oth._parameters) && object.Equals(this._inheritedParams, oth._inheritedParams);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._parameters));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._inheritedParams));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.CallSignature.CallSignature";
      s += "(";
      s += Dafny.Helpers.ToString(this._parameters);
      s += ", ";
      s += Dafny.Helpers.ToString(this._inheritedParams);
      s += ")";
      return s;
    }
    private static readonly DAST._ICallSignature theDefault = create(Dafny.Sequence<DAST._IFormal>.Empty, Dafny.Sequence<DAST._IFormal>.Empty);
    public static DAST._ICallSignature Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._ICallSignature> _TYPE = new Dafny.TypeDescriptor<DAST._ICallSignature>(DAST.CallSignature.Default());
    public static Dafny.TypeDescriptor<DAST._ICallSignature> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICallSignature create(Dafny.ISequence<DAST._IFormal> parameters, Dafny.ISequence<DAST._IFormal> inheritedParams) {
      return new CallSignature(parameters, inheritedParams);
    }
    public static _ICallSignature create_CallSignature(Dafny.ISequence<DAST._IFormal> parameters, Dafny.ISequence<DAST._IFormal> inheritedParams) {
      return create(parameters, inheritedParams);
    }
    public bool is_CallSignature { get { return true; } }
    public Dafny.ISequence<DAST._IFormal> dtor_parameters {
      get {
        return this._parameters;
      }
    }
    public Dafny.ISequence<DAST._IFormal> dtor_inheritedParams {
      get {
        return this._inheritedParams;
      }
    }
  }

  public interface _ICallName {
    bool is_CallName { get; }
    bool is_MapBuilderAdd { get; }
    bool is_MapBuilderBuild { get; }
    bool is_SetBuilderAdd { get; }
    bool is_SetBuilderBuild { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Std.Wrappers._IOption<DAST._IType> dtor_onType { get; }
    Std.Wrappers._IOption<DAST._IFormal> dtor_receiverArg { get; }
    bool dtor_receiverAsArgument { get; }
    DAST._ICallSignature dtor_signature { get; }
    _ICallName DowncastClone();
  }
  public abstract class CallName : _ICallName {
    public CallName() {
    }
    private static readonly DAST._ICallName theDefault = create_CallName(Dafny.Sequence<Dafny.Rune>.Empty, Std.Wrappers.Option<DAST._IType>.Default(), Std.Wrappers.Option<DAST._IFormal>.Default(), false, DAST.CallSignature.Default());
    public static DAST._ICallName Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._ICallName> _TYPE = new Dafny.TypeDescriptor<DAST._ICallName>(DAST.CallName.Default());
    public static Dafny.TypeDescriptor<DAST._ICallName> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICallName create_CallName(Dafny.ISequence<Dafny.Rune> name, Std.Wrappers._IOption<DAST._IType> onType, Std.Wrappers._IOption<DAST._IFormal> receiverArg, bool receiverAsArgument, DAST._ICallSignature signature) {
      return new CallName_CallName(name, onType, receiverArg, receiverAsArgument, signature);
    }
    public static _ICallName create_MapBuilderAdd() {
      return new CallName_MapBuilderAdd();
    }
    public static _ICallName create_MapBuilderBuild() {
      return new CallName_MapBuilderBuild();
    }
    public static _ICallName create_SetBuilderAdd() {
      return new CallName_SetBuilderAdd();
    }
    public static _ICallName create_SetBuilderBuild() {
      return new CallName_SetBuilderBuild();
    }
    public bool is_CallName { get { return this is CallName_CallName; } }
    public bool is_MapBuilderAdd { get { return this is CallName_MapBuilderAdd; } }
    public bool is_MapBuilderBuild { get { return this is CallName_MapBuilderBuild; } }
    public bool is_SetBuilderAdd { get { return this is CallName_SetBuilderAdd; } }
    public bool is_SetBuilderBuild { get { return this is CallName_SetBuilderBuild; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        return ((CallName_CallName)d)._name;
      }
    }
    public Std.Wrappers._IOption<DAST._IType> dtor_onType {
      get {
        var d = this;
        return ((CallName_CallName)d)._onType;
      }
    }
    public Std.Wrappers._IOption<DAST._IFormal> dtor_receiverArg {
      get {
        var d = this;
        return ((CallName_CallName)d)._receiverArg;
      }
    }
    public bool dtor_receiverAsArgument {
      get {
        var d = this;
        return ((CallName_CallName)d)._receiverAsArgument;
      }
    }
    public DAST._ICallSignature dtor_signature {
      get {
        var d = this;
        return ((CallName_CallName)d)._signature;
      }
    }
    public abstract _ICallName DowncastClone();
  }
  public class CallName_CallName : CallName {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Std.Wrappers._IOption<DAST._IType> _onType;
    public readonly Std.Wrappers._IOption<DAST._IFormal> _receiverArg;
    public readonly bool _receiverAsArgument;
    public readonly DAST._ICallSignature _signature;
    public CallName_CallName(Dafny.ISequence<Dafny.Rune> name, Std.Wrappers._IOption<DAST._IType> onType, Std.Wrappers._IOption<DAST._IFormal> receiverArg, bool receiverAsArgument, DAST._ICallSignature signature) : base() {
      this._name = name;
      this._onType = onType;
      this._receiverArg = receiverArg;
      this._receiverAsArgument = receiverAsArgument;
      this._signature = signature;
    }
    public override _ICallName DowncastClone() {
      if (this is _ICallName dt) { return dt; }
      return new CallName_CallName(_name, _onType, _receiverArg, _receiverAsArgument, _signature);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.CallName_CallName;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._onType, oth._onType) && object.Equals(this._receiverArg, oth._receiverArg) && this._receiverAsArgument == oth._receiverAsArgument && object.Equals(this._signature, oth._signature);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._onType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._receiverArg));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._receiverAsArgument));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._signature));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.CallName.CallName";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._onType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._receiverArg);
      s += ", ";
      s += Dafny.Helpers.ToString(this._receiverAsArgument);
      s += ", ";
      s += Dafny.Helpers.ToString(this._signature);
      s += ")";
      return s;
    }
  }
  public class CallName_MapBuilderAdd : CallName {
    public CallName_MapBuilderAdd() : base() {
    }
    public override _ICallName DowncastClone() {
      if (this is _ICallName dt) { return dt; }
      return new CallName_MapBuilderAdd();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.CallName_MapBuilderAdd;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.CallName.MapBuilderAdd";
      return s;
    }
  }
  public class CallName_MapBuilderBuild : CallName {
    public CallName_MapBuilderBuild() : base() {
    }
    public override _ICallName DowncastClone() {
      if (this is _ICallName dt) { return dt; }
      return new CallName_MapBuilderBuild();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.CallName_MapBuilderBuild;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.CallName.MapBuilderBuild";
      return s;
    }
  }
  public class CallName_SetBuilderAdd : CallName {
    public CallName_SetBuilderAdd() : base() {
    }
    public override _ICallName DowncastClone() {
      if (this is _ICallName dt) { return dt; }
      return new CallName_SetBuilderAdd();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.CallName_SetBuilderAdd;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.CallName.SetBuilderAdd";
      return s;
    }
  }
  public class CallName_SetBuilderBuild : CallName {
    public CallName_SetBuilderBuild() : base() {
    }
    public override _ICallName DowncastClone() {
      if (this is _ICallName dt) { return dt; }
      return new CallName_SetBuilderBuild();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.CallName_SetBuilderBuild;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.CallName.SetBuilderBuild";
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
    bool is_ConstructorNewSeparator { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    DAST._IType dtor_typ { get; }
    Std.Wrappers._IOption<DAST._IExpression> dtor_maybeValue { get; }
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
    DAST._ICallName dtor_callName { get; }
    Dafny.ISequence<DAST._IType> dtor_typeArgs { get; }
    Dafny.ISequence<DAST._IExpression> dtor_args { get; }
    Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> dtor_outs { get; }
    DAST._IExpression dtor_expr { get; }
    Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> dtor_toLabel { get; }
    DAST._IExpression dtor_Print_a0 { get; }
    Dafny.ISequence<DAST._IField> dtor_fields { get; }
    _IStatement DowncastClone();
  }
  public abstract class Statement : _IStatement {
    public Statement() {
    }
    private static readonly DAST._IStatement theDefault = create_DeclareVar(Dafny.Sequence<Dafny.Rune>.Empty, DAST.Type.Default(), Std.Wrappers.Option<DAST._IExpression>.Default());
    public static DAST._IStatement Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IStatement> _TYPE = new Dafny.TypeDescriptor<DAST._IStatement>(DAST.Statement.Default());
    public static Dafny.TypeDescriptor<DAST._IStatement> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStatement create_DeclareVar(Dafny.ISequence<Dafny.Rune> name, DAST._IType typ, Std.Wrappers._IOption<DAST._IExpression> maybeValue) {
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
    public static _IStatement create_Call(DAST._IExpression @on, DAST._ICallName callName, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> outs) {
      return new Statement_Call(@on, callName, typeArgs, args, outs);
    }
    public static _IStatement create_Return(DAST._IExpression expr) {
      return new Statement_Return(expr);
    }
    public static _IStatement create_EarlyReturn() {
      return new Statement_EarlyReturn();
    }
    public static _IStatement create_Break(Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> toLabel) {
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
    public static _IStatement create_ConstructorNewSeparator(Dafny.ISequence<DAST._IField> fields) {
      return new Statement_ConstructorNewSeparator(fields);
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
    public bool is_ConstructorNewSeparator { get { return this is Statement_ConstructorNewSeparator; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        return ((Statement_DeclareVar)d)._name;
      }
    }
    public DAST._IType dtor_typ {
      get {
        var d = this;
        return ((Statement_DeclareVar)d)._typ;
      }
    }
    public Std.Wrappers._IOption<DAST._IExpression> dtor_maybeValue {
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
    public DAST._ICallName dtor_callName {
      get {
        var d = this;
        return ((Statement_Call)d)._callName;
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
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> dtor_outs {
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
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> dtor_toLabel {
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
    public Dafny.ISequence<DAST._IField> dtor_fields {
      get {
        var d = this;
        return ((Statement_ConstructorNewSeparator)d)._fields;
      }
    }
    public abstract _IStatement DowncastClone();
  }
  public class Statement_DeclareVar : Statement {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly DAST._IType _typ;
    public readonly Std.Wrappers._IOption<DAST._IExpression> _maybeValue;
    public Statement_DeclareVar(Dafny.ISequence<Dafny.Rune> name, DAST._IType typ, Std.Wrappers._IOption<DAST._IExpression> maybeValue) : base() {
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
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.DeclareVar";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
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
      return (int) hash;
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
      return (int) hash;
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
      return (int) hash;
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
      return (int) hash;
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
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Foreach";
      s += "(";
      s += Dafny.Helpers.ToString(this._boundName);
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
    public readonly DAST._ICallName _callName;
    public readonly Dafny.ISequence<DAST._IType> _typeArgs;
    public readonly Dafny.ISequence<DAST._IExpression> _args;
    public readonly Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _outs;
    public Statement_Call(DAST._IExpression @on, DAST._ICallName callName, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> outs) : base() {
      this._on = @on;
      this._callName = callName;
      this._typeArgs = typeArgs;
      this._args = args;
      this._outs = outs;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_Call(_on, _callName, _typeArgs, _args, _outs);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_Call;
      return oth != null && object.Equals(this._on, oth._on) && object.Equals(this._callName, oth._callName) && object.Equals(this._typeArgs, oth._typeArgs) && object.Equals(this._args, oth._args) && object.Equals(this._outs, oth._outs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._on));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._callName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeArgs));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._args));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._outs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Call";
      s += "(";
      s += Dafny.Helpers.ToString(this._on);
      s += ", ";
      s += Dafny.Helpers.ToString(this._callName);
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
      return (int) hash;
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
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.EarlyReturn";
      return s;
    }
  }
  public class Statement_Break : Statement {
    public readonly Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _toLabel;
    public Statement_Break(Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> toLabel) : base() {
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
      return (int) hash;
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
      return (int) hash;
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
      return (int) hash;
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
      return (int) hash;
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
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Print";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class Statement_ConstructorNewSeparator : Statement {
    public readonly Dafny.ISequence<DAST._IField> _fields;
    public Statement_ConstructorNewSeparator(Dafny.ISequence<DAST._IField> fields) : base() {
      this._fields = fields;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_ConstructorNewSeparator(_fields);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_ConstructorNewSeparator;
      return oth != null && object.Equals(this._fields, oth._fields);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 14;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fields));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.ConstructorNewSeparator";
      s += "(";
      s += Dafny.Helpers.ToString(this._fields);
      s += ")";
      return s;
    }
  }

  public interface _IAssignLhs {
    bool is_Ident { get; }
    bool is_Select { get; }
    bool is_Index { get; }
    Dafny.ISequence<Dafny.Rune> dtor_ident { get; }
    DAST._IExpression dtor_expr { get; }
    Dafny.ISequence<Dafny.Rune> dtor_field { get; }
    bool dtor_isConstant { get; }
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
    public static _IAssignLhs create_Ident(Dafny.ISequence<Dafny.Rune> ident) {
      return new AssignLhs_Ident(ident);
    }
    public static _IAssignLhs create_Select(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, bool isConstant) {
      return new AssignLhs_Select(expr, field, isConstant);
    }
    public static _IAssignLhs create_Index(DAST._IExpression expr, Dafny.ISequence<DAST._IExpression> indices) {
      return new AssignLhs_Index(expr, indices);
    }
    public bool is_Ident { get { return this is AssignLhs_Ident; } }
    public bool is_Select { get { return this is AssignLhs_Select; } }
    public bool is_Index { get { return this is AssignLhs_Index; } }
    public Dafny.ISequence<Dafny.Rune> dtor_ident {
      get {
        var d = this;
        return ((AssignLhs_Ident)d)._ident;
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
    public bool dtor_isConstant {
      get {
        var d = this;
        return ((AssignLhs_Select)d)._isConstant;
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
    public readonly Dafny.ISequence<Dafny.Rune> _ident;
    public AssignLhs_Ident(Dafny.ISequence<Dafny.Rune> ident) : base() {
      this._ident = ident;
    }
    public override _IAssignLhs DowncastClone() {
      if (this is _IAssignLhs dt) { return dt; }
      return new AssignLhs_Ident(_ident);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.AssignLhs_Ident;
      return oth != null && object.Equals(this._ident, oth._ident);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ident));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.AssignLhs.Ident";
      s += "(";
      s += Dafny.Helpers.ToString(this._ident);
      s += ")";
      return s;
    }
  }
  public class AssignLhs_Select : AssignLhs {
    public readonly DAST._IExpression _expr;
    public readonly Dafny.ISequence<Dafny.Rune> _field;
    public readonly bool _isConstant;
    public AssignLhs_Select(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, bool isConstant) : base() {
      this._expr = expr;
      this._field = field;
      this._isConstant = isConstant;
    }
    public override _IAssignLhs DowncastClone() {
      if (this is _IAssignLhs dt) { return dt; }
      return new AssignLhs_Select(_expr, _field, _isConstant);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.AssignLhs_Select;
      return oth != null && object.Equals(this._expr, oth._expr) && object.Equals(this._field, oth._field) && this._isConstant == oth._isConstant;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._field));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._isConstant));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.AssignLhs.Select";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._field);
      s += ", ";
      s += Dafny.Helpers.ToString(this._isConstant);
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
      return (int) hash;
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
      return (int) hash;
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
      return (int) hash;
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
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.CollKind.Map";
      return s;
    }
  }

  public interface _ITypedBinOp {
    bool is_TypedBinOp { get; }
    DAST._IBinOp dtor_op { get; }
    DAST._IType dtor_leftType { get; }
    DAST._IType dtor_rightType { get; }
    DAST._IType dtor_resultType { get; }
    _ITypedBinOp DowncastClone();
  }
  public class TypedBinOp : _ITypedBinOp {
    public readonly DAST._IBinOp _op;
    public readonly DAST._IType _leftType;
    public readonly DAST._IType _rightType;
    public readonly DAST._IType _resultType;
    public TypedBinOp(DAST._IBinOp op, DAST._IType leftType, DAST._IType rightType, DAST._IType resultType) {
      this._op = op;
      this._leftType = leftType;
      this._rightType = rightType;
      this._resultType = resultType;
    }
    public _ITypedBinOp DowncastClone() {
      if (this is _ITypedBinOp dt) { return dt; }
      return new TypedBinOp(_op, _leftType, _rightType, _resultType);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.TypedBinOp;
      return oth != null && object.Equals(this._op, oth._op) && object.Equals(this._leftType, oth._leftType) && object.Equals(this._rightType, oth._rightType) && object.Equals(this._resultType, oth._resultType);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._op));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._leftType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._rightType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._resultType));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.TypedBinOp.TypedBinOp";
      s += "(";
      s += Dafny.Helpers.ToString(this._op);
      s += ", ";
      s += Dafny.Helpers.ToString(this._leftType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._rightType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._resultType);
      s += ")";
      return s;
    }
    private static readonly DAST._ITypedBinOp theDefault = create(DAST.BinOp.Default(), DAST.Type.Default(), DAST.Type.Default(), DAST.Type.Default());
    public static DAST._ITypedBinOp Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._ITypedBinOp> _TYPE = new Dafny.TypeDescriptor<DAST._ITypedBinOp>(DAST.TypedBinOp.Default());
    public static Dafny.TypeDescriptor<DAST._ITypedBinOp> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITypedBinOp create(DAST._IBinOp op, DAST._IType leftType, DAST._IType rightType, DAST._IType resultType) {
      return new TypedBinOp(op, leftType, rightType, resultType);
    }
    public static _ITypedBinOp create_TypedBinOp(DAST._IBinOp op, DAST._IType leftType, DAST._IType rightType, DAST._IType resultType) {
      return create(op, leftType, rightType, resultType);
    }
    public bool is_TypedBinOp { get { return true; } }
    public DAST._IBinOp dtor_op {
      get {
        return this._op;
      }
    }
    public DAST._IType dtor_leftType {
      get {
        return this._leftType;
      }
    }
    public DAST._IType dtor_rightType {
      get {
        return this._rightType;
      }
    }
    public DAST._IType dtor_resultType {
      get {
        return this._resultType;
      }
    }
  }

  public interface _IBinOp {
    bool is_Eq { get; }
    bool is_Div { get; }
    bool is_EuclidianDiv { get; }
    bool is_Mod { get; }
    bool is_EuclidianMod { get; }
    bool is_Lt { get; }
    bool is_LtChar { get; }
    bool is_Plus { get; }
    bool is_Minus { get; }
    bool is_Times { get; }
    bool is_BitwiseAnd { get; }
    bool is_BitwiseOr { get; }
    bool is_BitwiseXor { get; }
    bool is_BitwiseShiftRight { get; }
    bool is_BitwiseShiftLeft { get; }
    bool is_And { get; }
    bool is_Or { get; }
    bool is_In { get; }
    bool is_SeqProperPrefix { get; }
    bool is_SeqPrefix { get; }
    bool is_SetMerge { get; }
    bool is_SetSubtraction { get; }
    bool is_SetIntersection { get; }
    bool is_Subset { get; }
    bool is_ProperSubset { get; }
    bool is_SetDisjoint { get; }
    bool is_MapMerge { get; }
    bool is_MapSubtraction { get; }
    bool is_MultisetMerge { get; }
    bool is_MultisetSubtraction { get; }
    bool is_MultisetIntersection { get; }
    bool is_Submultiset { get; }
    bool is_ProperSubmultiset { get; }
    bool is_MultisetDisjoint { get; }
    bool is_Concat { get; }
    bool is_Passthrough { get; }
    bool dtor_referential { get; }
    bool dtor_overflow { get; }
    Dafny.ISequence<Dafny.Rune> dtor_Passthrough_a0 { get; }
    _IBinOp DowncastClone();
  }
  public abstract class BinOp : _IBinOp {
    public BinOp() {
    }
    private static readonly DAST._IBinOp theDefault = create_Eq(false);
    public static DAST._IBinOp Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IBinOp> _TYPE = new Dafny.TypeDescriptor<DAST._IBinOp>(DAST.BinOp.Default());
    public static Dafny.TypeDescriptor<DAST._IBinOp> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IBinOp create_Eq(bool referential) {
      return new BinOp_Eq(referential);
    }
    public static _IBinOp create_Div(bool overflow) {
      return new BinOp_Div(overflow);
    }
    public static _IBinOp create_EuclidianDiv() {
      return new BinOp_EuclidianDiv();
    }
    public static _IBinOp create_Mod() {
      return new BinOp_Mod();
    }
    public static _IBinOp create_EuclidianMod() {
      return new BinOp_EuclidianMod();
    }
    public static _IBinOp create_Lt() {
      return new BinOp_Lt();
    }
    public static _IBinOp create_LtChar() {
      return new BinOp_LtChar();
    }
    public static _IBinOp create_Plus(bool overflow) {
      return new BinOp_Plus(overflow);
    }
    public static _IBinOp create_Minus(bool overflow) {
      return new BinOp_Minus(overflow);
    }
    public static _IBinOp create_Times(bool overflow) {
      return new BinOp_Times(overflow);
    }
    public static _IBinOp create_BitwiseAnd() {
      return new BinOp_BitwiseAnd();
    }
    public static _IBinOp create_BitwiseOr() {
      return new BinOp_BitwiseOr();
    }
    public static _IBinOp create_BitwiseXor() {
      return new BinOp_BitwiseXor();
    }
    public static _IBinOp create_BitwiseShiftRight() {
      return new BinOp_BitwiseShiftRight();
    }
    public static _IBinOp create_BitwiseShiftLeft() {
      return new BinOp_BitwiseShiftLeft();
    }
    public static _IBinOp create_And() {
      return new BinOp_And();
    }
    public static _IBinOp create_Or() {
      return new BinOp_Or();
    }
    public static _IBinOp create_In() {
      return new BinOp_In();
    }
    public static _IBinOp create_SeqProperPrefix() {
      return new BinOp_SeqProperPrefix();
    }
    public static _IBinOp create_SeqPrefix() {
      return new BinOp_SeqPrefix();
    }
    public static _IBinOp create_SetMerge() {
      return new BinOp_SetMerge();
    }
    public static _IBinOp create_SetSubtraction() {
      return new BinOp_SetSubtraction();
    }
    public static _IBinOp create_SetIntersection() {
      return new BinOp_SetIntersection();
    }
    public static _IBinOp create_Subset() {
      return new BinOp_Subset();
    }
    public static _IBinOp create_ProperSubset() {
      return new BinOp_ProperSubset();
    }
    public static _IBinOp create_SetDisjoint() {
      return new BinOp_SetDisjoint();
    }
    public static _IBinOp create_MapMerge() {
      return new BinOp_MapMerge();
    }
    public static _IBinOp create_MapSubtraction() {
      return new BinOp_MapSubtraction();
    }
    public static _IBinOp create_MultisetMerge() {
      return new BinOp_MultisetMerge();
    }
    public static _IBinOp create_MultisetSubtraction() {
      return new BinOp_MultisetSubtraction();
    }
    public static _IBinOp create_MultisetIntersection() {
      return new BinOp_MultisetIntersection();
    }
    public static _IBinOp create_Submultiset() {
      return new BinOp_Submultiset();
    }
    public static _IBinOp create_ProperSubmultiset() {
      return new BinOp_ProperSubmultiset();
    }
    public static _IBinOp create_MultisetDisjoint() {
      return new BinOp_MultisetDisjoint();
    }
    public static _IBinOp create_Concat() {
      return new BinOp_Concat();
    }
    public static _IBinOp create_Passthrough(Dafny.ISequence<Dafny.Rune> _a0) {
      return new BinOp_Passthrough(_a0);
    }
    public bool is_Eq { get { return this is BinOp_Eq; } }
    public bool is_Div { get { return this is BinOp_Div; } }
    public bool is_EuclidianDiv { get { return this is BinOp_EuclidianDiv; } }
    public bool is_Mod { get { return this is BinOp_Mod; } }
    public bool is_EuclidianMod { get { return this is BinOp_EuclidianMod; } }
    public bool is_Lt { get { return this is BinOp_Lt; } }
    public bool is_LtChar { get { return this is BinOp_LtChar; } }
    public bool is_Plus { get { return this is BinOp_Plus; } }
    public bool is_Minus { get { return this is BinOp_Minus; } }
    public bool is_Times { get { return this is BinOp_Times; } }
    public bool is_BitwiseAnd { get { return this is BinOp_BitwiseAnd; } }
    public bool is_BitwiseOr { get { return this is BinOp_BitwiseOr; } }
    public bool is_BitwiseXor { get { return this is BinOp_BitwiseXor; } }
    public bool is_BitwiseShiftRight { get { return this is BinOp_BitwiseShiftRight; } }
    public bool is_BitwiseShiftLeft { get { return this is BinOp_BitwiseShiftLeft; } }
    public bool is_And { get { return this is BinOp_And; } }
    public bool is_Or { get { return this is BinOp_Or; } }
    public bool is_In { get { return this is BinOp_In; } }
    public bool is_SeqProperPrefix { get { return this is BinOp_SeqProperPrefix; } }
    public bool is_SeqPrefix { get { return this is BinOp_SeqPrefix; } }
    public bool is_SetMerge { get { return this is BinOp_SetMerge; } }
    public bool is_SetSubtraction { get { return this is BinOp_SetSubtraction; } }
    public bool is_SetIntersection { get { return this is BinOp_SetIntersection; } }
    public bool is_Subset { get { return this is BinOp_Subset; } }
    public bool is_ProperSubset { get { return this is BinOp_ProperSubset; } }
    public bool is_SetDisjoint { get { return this is BinOp_SetDisjoint; } }
    public bool is_MapMerge { get { return this is BinOp_MapMerge; } }
    public bool is_MapSubtraction { get { return this is BinOp_MapSubtraction; } }
    public bool is_MultisetMerge { get { return this is BinOp_MultisetMerge; } }
    public bool is_MultisetSubtraction { get { return this is BinOp_MultisetSubtraction; } }
    public bool is_MultisetIntersection { get { return this is BinOp_MultisetIntersection; } }
    public bool is_Submultiset { get { return this is BinOp_Submultiset; } }
    public bool is_ProperSubmultiset { get { return this is BinOp_ProperSubmultiset; } }
    public bool is_MultisetDisjoint { get { return this is BinOp_MultisetDisjoint; } }
    public bool is_Concat { get { return this is BinOp_Concat; } }
    public bool is_Passthrough { get { return this is BinOp_Passthrough; } }
    public bool dtor_referential {
      get {
        var d = this;
        return ((BinOp_Eq)d)._referential;
      }
    }
    public bool dtor_overflow {
      get {
        var d = this;
        if (d is BinOp_Div) { return ((BinOp_Div)d)._overflow; }
        if (d is BinOp_Plus) { return ((BinOp_Plus)d)._overflow; }
        if (d is BinOp_Minus) { return ((BinOp_Minus)d)._overflow; }
        return ((BinOp_Times)d)._overflow;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_Passthrough_a0 {
      get {
        var d = this;
        return ((BinOp_Passthrough)d)._a0;
      }
    }
    public abstract _IBinOp DowncastClone();
  }
  public class BinOp_Eq : BinOp {
    public readonly bool _referential;
    public BinOp_Eq(bool referential) : base() {
      this._referential = referential;
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Eq(_referential);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Eq;
      return oth != null && this._referential == oth._referential;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._referential));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Eq";
      s += "(";
      s += Dafny.Helpers.ToString(this._referential);
      s += ")";
      return s;
    }
  }
  public class BinOp_Div : BinOp {
    public readonly bool _overflow;
    public BinOp_Div(bool overflow) : base() {
      this._overflow = overflow;
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Div(_overflow);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Div;
      return oth != null && this._overflow == oth._overflow;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overflow));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Div";
      s += "(";
      s += Dafny.Helpers.ToString(this._overflow);
      s += ")";
      return s;
    }
  }
  public class BinOp_EuclidianDiv : BinOp {
    public BinOp_EuclidianDiv() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_EuclidianDiv();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_EuclidianDiv;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.EuclidianDiv";
      return s;
    }
  }
  public class BinOp_Mod : BinOp {
    public BinOp_Mod() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Mod();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Mod;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Mod";
      return s;
    }
  }
  public class BinOp_EuclidianMod : BinOp {
    public BinOp_EuclidianMod() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_EuclidianMod();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_EuclidianMod;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.EuclidianMod";
      return s;
    }
  }
  public class BinOp_Lt : BinOp {
    public BinOp_Lt() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Lt();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Lt;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Lt";
      return s;
    }
  }
  public class BinOp_LtChar : BinOp {
    public BinOp_LtChar() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_LtChar();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_LtChar;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.LtChar";
      return s;
    }
  }
  public class BinOp_Plus : BinOp {
    public readonly bool _overflow;
    public BinOp_Plus(bool overflow) : base() {
      this._overflow = overflow;
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Plus(_overflow);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Plus;
      return oth != null && this._overflow == oth._overflow;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overflow));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Plus";
      s += "(";
      s += Dafny.Helpers.ToString(this._overflow);
      s += ")";
      return s;
    }
  }
  public class BinOp_Minus : BinOp {
    public readonly bool _overflow;
    public BinOp_Minus(bool overflow) : base() {
      this._overflow = overflow;
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Minus(_overflow);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Minus;
      return oth != null && this._overflow == oth._overflow;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overflow));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Minus";
      s += "(";
      s += Dafny.Helpers.ToString(this._overflow);
      s += ")";
      return s;
    }
  }
  public class BinOp_Times : BinOp {
    public readonly bool _overflow;
    public BinOp_Times(bool overflow) : base() {
      this._overflow = overflow;
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Times(_overflow);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Times;
      return oth != null && this._overflow == oth._overflow;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overflow));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Times";
      s += "(";
      s += Dafny.Helpers.ToString(this._overflow);
      s += ")";
      return s;
    }
  }
  public class BinOp_BitwiseAnd : BinOp {
    public BinOp_BitwiseAnd() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_BitwiseAnd();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_BitwiseAnd;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 10;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.BitwiseAnd";
      return s;
    }
  }
  public class BinOp_BitwiseOr : BinOp {
    public BinOp_BitwiseOr() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_BitwiseOr();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_BitwiseOr;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 11;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.BitwiseOr";
      return s;
    }
  }
  public class BinOp_BitwiseXor : BinOp {
    public BinOp_BitwiseXor() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_BitwiseXor();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_BitwiseXor;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 12;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.BitwiseXor";
      return s;
    }
  }
  public class BinOp_BitwiseShiftRight : BinOp {
    public BinOp_BitwiseShiftRight() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_BitwiseShiftRight();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_BitwiseShiftRight;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 13;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.BitwiseShiftRight";
      return s;
    }
  }
  public class BinOp_BitwiseShiftLeft : BinOp {
    public BinOp_BitwiseShiftLeft() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_BitwiseShiftLeft();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_BitwiseShiftLeft;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 14;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.BitwiseShiftLeft";
      return s;
    }
  }
  public class BinOp_And : BinOp {
    public BinOp_And() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_And();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_And;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 15;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.And";
      return s;
    }
  }
  public class BinOp_Or : BinOp {
    public BinOp_Or() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Or();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Or;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 16;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Or";
      return s;
    }
  }
  public class BinOp_In : BinOp {
    public BinOp_In() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_In();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_In;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 17;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.In";
      return s;
    }
  }
  public class BinOp_SeqProperPrefix : BinOp {
    public BinOp_SeqProperPrefix() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_SeqProperPrefix();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_SeqProperPrefix;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 18;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.SeqProperPrefix";
      return s;
    }
  }
  public class BinOp_SeqPrefix : BinOp {
    public BinOp_SeqPrefix() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_SeqPrefix();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_SeqPrefix;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 19;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.SeqPrefix";
      return s;
    }
  }
  public class BinOp_SetMerge : BinOp {
    public BinOp_SetMerge() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_SetMerge();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_SetMerge;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 20;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.SetMerge";
      return s;
    }
  }
  public class BinOp_SetSubtraction : BinOp {
    public BinOp_SetSubtraction() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_SetSubtraction();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_SetSubtraction;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 21;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.SetSubtraction";
      return s;
    }
  }
  public class BinOp_SetIntersection : BinOp {
    public BinOp_SetIntersection() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_SetIntersection();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_SetIntersection;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 22;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.SetIntersection";
      return s;
    }
  }
  public class BinOp_Subset : BinOp {
    public BinOp_Subset() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Subset();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Subset;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 23;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Subset";
      return s;
    }
  }
  public class BinOp_ProperSubset : BinOp {
    public BinOp_ProperSubset() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_ProperSubset();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_ProperSubset;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 24;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.ProperSubset";
      return s;
    }
  }
  public class BinOp_SetDisjoint : BinOp {
    public BinOp_SetDisjoint() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_SetDisjoint();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_SetDisjoint;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 25;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.SetDisjoint";
      return s;
    }
  }
  public class BinOp_MapMerge : BinOp {
    public BinOp_MapMerge() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_MapMerge();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_MapMerge;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 26;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.MapMerge";
      return s;
    }
  }
  public class BinOp_MapSubtraction : BinOp {
    public BinOp_MapSubtraction() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_MapSubtraction();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_MapSubtraction;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 27;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.MapSubtraction";
      return s;
    }
  }
  public class BinOp_MultisetMerge : BinOp {
    public BinOp_MultisetMerge() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_MultisetMerge();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_MultisetMerge;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 28;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.MultisetMerge";
      return s;
    }
  }
  public class BinOp_MultisetSubtraction : BinOp {
    public BinOp_MultisetSubtraction() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_MultisetSubtraction();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_MultisetSubtraction;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 29;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.MultisetSubtraction";
      return s;
    }
  }
  public class BinOp_MultisetIntersection : BinOp {
    public BinOp_MultisetIntersection() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_MultisetIntersection();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_MultisetIntersection;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 30;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.MultisetIntersection";
      return s;
    }
  }
  public class BinOp_Submultiset : BinOp {
    public BinOp_Submultiset() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Submultiset();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Submultiset;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 31;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Submultiset";
      return s;
    }
  }
  public class BinOp_ProperSubmultiset : BinOp {
    public BinOp_ProperSubmultiset() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_ProperSubmultiset();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_ProperSubmultiset;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 32;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.ProperSubmultiset";
      return s;
    }
  }
  public class BinOp_MultisetDisjoint : BinOp {
    public BinOp_MultisetDisjoint() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_MultisetDisjoint();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_MultisetDisjoint;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 33;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.MultisetDisjoint";
      return s;
    }
  }
  public class BinOp_Concat : BinOp {
    public BinOp_Concat() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Concat();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Concat;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 34;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Concat";
      return s;
    }
  }
  public class BinOp_Passthrough : BinOp {
    public readonly Dafny.ISequence<Dafny.Rune> _a0;
    public BinOp_Passthrough(Dafny.ISequence<Dafny.Rune> _a0) : base() {
      this._a0 = _a0;
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Passthrough(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Passthrough;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 35;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Passthrough";
      s += "(";
      s += this._a0.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }

  public interface _ISelectContext {
    bool is_SelectContextDatatype { get; }
    bool is_SelectContextGeneralTrait { get; }
    bool is_SelectContextClassOrObjectTrait { get; }
    _ISelectContext DowncastClone();
  }
  public abstract class SelectContext : _ISelectContext {
    public SelectContext() {
    }
    private static readonly DAST._ISelectContext theDefault = create_SelectContextDatatype();
    public static DAST._ISelectContext Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._ISelectContext> _TYPE = new Dafny.TypeDescriptor<DAST._ISelectContext>(DAST.SelectContext.Default());
    public static Dafny.TypeDescriptor<DAST._ISelectContext> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISelectContext create_SelectContextDatatype() {
      return new SelectContext_SelectContextDatatype();
    }
    public static _ISelectContext create_SelectContextGeneralTrait() {
      return new SelectContext_SelectContextGeneralTrait();
    }
    public static _ISelectContext create_SelectContextClassOrObjectTrait() {
      return new SelectContext_SelectContextClassOrObjectTrait();
    }
    public bool is_SelectContextDatatype { get { return this is SelectContext_SelectContextDatatype; } }
    public bool is_SelectContextGeneralTrait { get { return this is SelectContext_SelectContextGeneralTrait; } }
    public bool is_SelectContextClassOrObjectTrait { get { return this is SelectContext_SelectContextClassOrObjectTrait; } }
    public static System.Collections.Generic.IEnumerable<_ISelectContext> AllSingletonConstructors {
      get {
        yield return SelectContext.create_SelectContextDatatype();
        yield return SelectContext.create_SelectContextGeneralTrait();
        yield return SelectContext.create_SelectContextClassOrObjectTrait();
      }
    }
    public abstract _ISelectContext DowncastClone();
  }
  public class SelectContext_SelectContextDatatype : SelectContext {
    public SelectContext_SelectContextDatatype() : base() {
    }
    public override _ISelectContext DowncastClone() {
      if (this is _ISelectContext dt) { return dt; }
      return new SelectContext_SelectContextDatatype();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.SelectContext_SelectContextDatatype;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.SelectContext.SelectContextDatatype";
      return s;
    }
  }
  public class SelectContext_SelectContextGeneralTrait : SelectContext {
    public SelectContext_SelectContextGeneralTrait() : base() {
    }
    public override _ISelectContext DowncastClone() {
      if (this is _ISelectContext dt) { return dt; }
      return new SelectContext_SelectContextGeneralTrait();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.SelectContext_SelectContextGeneralTrait;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.SelectContext.SelectContextGeneralTrait";
      return s;
    }
  }
  public class SelectContext_SelectContextClassOrObjectTrait : SelectContext {
    public SelectContext_SelectContextClassOrObjectTrait() : base() {
    }
    public override _ISelectContext DowncastClone() {
      if (this is _ISelectContext dt) { return dt; }
      return new SelectContext_SelectContextClassOrObjectTrait();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.SelectContext_SelectContextClassOrObjectTrait;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.SelectContext.SelectContextClassOrObjectTrait";
      return s;
    }
  }

  public interface _IExpression {
    bool is_Literal { get; }
    bool is_Ident { get; }
    bool is_Companion { get; }
    bool is_ExternCompanion { get; }
    bool is_Tuple { get; }
    bool is_New { get; }
    bool is_NewUninitArray { get; }
    bool is_ArrayIndexToInt { get; }
    bool is_FinalizeNewArray { get; }
    bool is_DatatypeValue { get; }
    bool is_Convert { get; }
    bool is_SeqConstruct { get; }
    bool is_SeqValue { get; }
    bool is_SetValue { get; }
    bool is_MultisetValue { get; }
    bool is_MapValue { get; }
    bool is_MapBuilder { get; }
    bool is_SeqUpdate { get; }
    bool is_MapUpdate { get; }
    bool is_SetBuilder { get; }
    bool is_ToMultiset { get; }
    bool is_This { get; }
    bool is_Ite { get; }
    bool is_UnOp { get; }
    bool is_BinOp { get; }
    bool is_ArrayLen { get; }
    bool is_MapKeys { get; }
    bool is_MapValues { get; }
    bool is_MapItems { get; }
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
    bool is_Is { get; }
    bool is_InitializationValue { get; }
    bool is_BoolBoundedPool { get; }
    bool is_SetBoundedPool { get; }
    bool is_MapBoundedPool { get; }
    bool is_SeqBoundedPool { get; }
    bool is_MultisetBoundedPool { get; }
    bool is_ExactBoundedPool { get; }
    bool is_IntRange { get; }
    bool is_UnboundedIntRange { get; }
    bool is_Quantifier { get; }
    DAST._ILiteral dtor_Literal_a0 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_Companion_a0 { get; }
    Dafny.ISequence<DAST._IType> dtor_typeArgs { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_ExternCompanion_a0 { get; }
    Dafny.ISequence<DAST._IExpression> dtor_Tuple_a0 { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_path { get; }
    Dafny.ISequence<DAST._IExpression> dtor_args { get; }
    Dafny.ISequence<DAST._IExpression> dtor_dims { get; }
    DAST._IType dtor_typ { get; }
    DAST._IExpression dtor_value { get; }
    DAST._IResolvedType dtor_datatypeType { get; }
    Dafny.ISequence<Dafny.Rune> dtor_variant { get; }
    bool dtor_isCo { get; }
    Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> dtor_contents { get; }
    DAST._IType dtor_from { get; }
    DAST._IExpression dtor_length { get; }
    DAST._IExpression dtor_elem { get; }
    Dafny.ISequence<DAST._IExpression> dtor_elements { get; }
    Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> dtor_mapElems { get; }
    DAST._IType dtor_domainType { get; }
    DAST._IType dtor_rangeType { get; }
    DAST._IType dtor_keyType { get; }
    DAST._IType dtor_valueType { get; }
    DAST._IExpression dtor_expr { get; }
    DAST._IExpression dtor_indexExpr { get; }
    DAST._IType dtor_collectionType { get; }
    DAST._IType dtor_exprType { get; }
    DAST._IType dtor_elemType { get; }
    DAST._IExpression dtor_ToMultiset_a0 { get; }
    DAST._IExpression dtor_cond { get; }
    DAST._IExpression dtor_thn { get; }
    DAST._IExpression dtor_els { get; }
    DAST._IUnaryOp dtor_unOp { get; }
    DAST.Format._IUnaryOpFormat dtor_format1 { get; }
    DAST._ITypedBinOp dtor_op { get; }
    DAST._IExpression dtor_left { get; }
    DAST._IExpression dtor_right { get; }
    DAST.Format._IBinaryOpFormat dtor_format2 { get; }
    BigInteger dtor_dim { get; }
    bool dtor_native { get; }
    Dafny.ISequence<Dafny.Rune> dtor_field { get; }
    DAST._IFieldMutability dtor_fieldMutability { get; }
    DAST._ISelectContext dtor_selectContext { get; }
    DAST._IType dtor_isfieldType { get; }
    bool dtor_onDatatype { get; }
    bool dtor_isStatic { get; }
    bool dtor_isConstant { get; }
    Dafny.ISequence<DAST._IType> dtor_arguments { get; }
    DAST._ICollKind dtor_collKind { get; }
    Dafny.ISequence<DAST._IExpression> dtor_indices { get; }
    bool dtor_isArray { get; }
    Std.Wrappers._IOption<DAST._IExpression> dtor_low { get; }
    Std.Wrappers._IOption<DAST._IExpression> dtor_high { get; }
    BigInteger dtor_index { get; }
    DAST._IType dtor_fieldType { get; }
    DAST._IExpression dtor_on { get; }
    DAST._ICallName dtor_callName { get; }
    Dafny.ISequence<DAST._IFormal> dtor_params { get; }
    DAST._IType dtor_retType { get; }
    Dafny.ISequence<DAST._IStatement> dtor_body { get; }
    Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> dtor_values { get; }
    Dafny.ISequence<Dafny.Rune> dtor_ident { get; }
    DAST._IExpression dtor_iifeBody { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_dType { get; }
    DAST._IType dtor_fromType { get; }
    DAST._IType dtor_toType { get; }
    DAST._IExpression dtor_of { get; }
    bool dtor_includeDuplicates { get; }
    DAST._IExpression dtor_lo { get; }
    DAST._IExpression dtor_hi { get; }
    bool dtor_up { get; }
    DAST._IExpression dtor_start { get; }
    DAST._IExpression dtor_collection { get; }
    bool dtor_is__forall { get; }
    DAST._IExpression dtor_lambda { get; }
    _IExpression DowncastClone();
    bool IsThisUpcast();
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
    public static _IExpression create_Ident(Dafny.ISequence<Dafny.Rune> name) {
      return new Expression_Ident(name);
    }
    public static _IExpression create_Companion(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _a0, Dafny.ISequence<DAST._IType> typeArgs) {
      return new Expression_Companion(_a0, typeArgs);
    }
    public static _IExpression create_ExternCompanion(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _a0) {
      return new Expression_ExternCompanion(_a0);
    }
    public static _IExpression create_Tuple(Dafny.ISequence<DAST._IExpression> _a0) {
      return new Expression_Tuple(_a0);
    }
    public static _IExpression create_New(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args) {
      return new Expression_New(path, typeArgs, args);
    }
    public static _IExpression create_NewUninitArray(Dafny.ISequence<DAST._IExpression> dims, DAST._IType typ) {
      return new Expression_NewUninitArray(dims, typ);
    }
    public static _IExpression create_ArrayIndexToInt(DAST._IExpression @value) {
      return new Expression_ArrayIndexToInt(@value);
    }
    public static _IExpression create_FinalizeNewArray(DAST._IExpression @value, DAST._IType typ) {
      return new Expression_FinalizeNewArray(@value, typ);
    }
    public static _IExpression create_DatatypeValue(DAST._IResolvedType datatypeType, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<Dafny.Rune> variant, bool isCo, Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> contents) {
      return new Expression_DatatypeValue(datatypeType, typeArgs, variant, isCo, contents);
    }
    public static _IExpression create_Convert(DAST._IExpression @value, DAST._IType @from, DAST._IType typ) {
      return new Expression_Convert(@value, @from, typ);
    }
    public static _IExpression create_SeqConstruct(DAST._IExpression length, DAST._IExpression elem) {
      return new Expression_SeqConstruct(length, elem);
    }
    public static _IExpression create_SeqValue(Dafny.ISequence<DAST._IExpression> elements, DAST._IType typ) {
      return new Expression_SeqValue(elements, typ);
    }
    public static _IExpression create_SetValue(Dafny.ISequence<DAST._IExpression> elements) {
      return new Expression_SetValue(elements);
    }
    public static _IExpression create_MultisetValue(Dafny.ISequence<DAST._IExpression> elements) {
      return new Expression_MultisetValue(elements);
    }
    public static _IExpression create_MapValue(Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> mapElems, DAST._IType domainType, DAST._IType rangeType) {
      return new Expression_MapValue(mapElems, domainType, rangeType);
    }
    public static _IExpression create_MapBuilder(DAST._IType keyType, DAST._IType valueType) {
      return new Expression_MapBuilder(keyType, valueType);
    }
    public static _IExpression create_SeqUpdate(DAST._IExpression expr, DAST._IExpression indexExpr, DAST._IExpression @value, DAST._IType collectionType, DAST._IType exprType) {
      return new Expression_SeqUpdate(expr, indexExpr, @value, collectionType, exprType);
    }
    public static _IExpression create_MapUpdate(DAST._IExpression expr, DAST._IExpression indexExpr, DAST._IExpression @value, DAST._IType collectionType, DAST._IType exprType) {
      return new Expression_MapUpdate(expr, indexExpr, @value, collectionType, exprType);
    }
    public static _IExpression create_SetBuilder(DAST._IType elemType) {
      return new Expression_SetBuilder(elemType);
    }
    public static _IExpression create_ToMultiset(DAST._IExpression _a0) {
      return new Expression_ToMultiset(_a0);
    }
    public static _IExpression create_This() {
      return new Expression_This();
    }
    public static _IExpression create_Ite(DAST._IExpression cond, DAST._IExpression thn, DAST._IExpression els) {
      return new Expression_Ite(cond, thn, els);
    }
    public static _IExpression create_UnOp(DAST._IUnaryOp unOp, DAST._IExpression expr, DAST.Format._IUnaryOpFormat format1) {
      return new Expression_UnOp(unOp, expr, format1);
    }
    public static _IExpression create_BinOp(DAST._ITypedBinOp op, DAST._IExpression left, DAST._IExpression right, DAST.Format._IBinaryOpFormat format2) {
      return new Expression_BinOp(op, left, right, format2);
    }
    public static _IExpression create_ArrayLen(DAST._IExpression expr, DAST._IType exprType, BigInteger dim, bool native) {
      return new Expression_ArrayLen(expr, exprType, dim, native);
    }
    public static _IExpression create_MapKeys(DAST._IExpression expr) {
      return new Expression_MapKeys(expr);
    }
    public static _IExpression create_MapValues(DAST._IExpression expr) {
      return new Expression_MapValues(expr);
    }
    public static _IExpression create_MapItems(DAST._IExpression expr) {
      return new Expression_MapItems(expr);
    }
    public static _IExpression create_Select(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, DAST._IFieldMutability fieldMutability, DAST._ISelectContext selectContext, DAST._IType isfieldType) {
      return new Expression_Select(expr, field, fieldMutability, selectContext, isfieldType);
    }
    public static _IExpression create_SelectFn(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, bool onDatatype, bool isStatic, bool isConstant, Dafny.ISequence<DAST._IType> arguments) {
      return new Expression_SelectFn(expr, field, onDatatype, isStatic, isConstant, arguments);
    }
    public static _IExpression create_Index(DAST._IExpression expr, DAST._ICollKind collKind, Dafny.ISequence<DAST._IExpression> indices) {
      return new Expression_Index(expr, collKind, indices);
    }
    public static _IExpression create_IndexRange(DAST._IExpression expr, bool isArray, Std.Wrappers._IOption<DAST._IExpression> low, Std.Wrappers._IOption<DAST._IExpression> high) {
      return new Expression_IndexRange(expr, isArray, low, high);
    }
    public static _IExpression create_TupleSelect(DAST._IExpression expr, BigInteger index, DAST._IType fieldType) {
      return new Expression_TupleSelect(expr, index, fieldType);
    }
    public static _IExpression create_Call(DAST._IExpression @on, DAST._ICallName callName, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args) {
      return new Expression_Call(@on, callName, typeArgs, args);
    }
    public static _IExpression create_Lambda(Dafny.ISequence<DAST._IFormal> @params, DAST._IType retType, Dafny.ISequence<DAST._IStatement> body) {
      return new Expression_Lambda(@params, retType, body);
    }
    public static _IExpression create_BetaRedex(Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> values, DAST._IType retType, DAST._IExpression expr) {
      return new Expression_BetaRedex(values, retType, expr);
    }
    public static _IExpression create_IIFE(Dafny.ISequence<Dafny.Rune> ident, DAST._IType typ, DAST._IExpression @value, DAST._IExpression iifeBody) {
      return new Expression_IIFE(ident, typ, @value, iifeBody);
    }
    public static _IExpression create_Apply(DAST._IExpression expr, Dafny.ISequence<DAST._IExpression> args) {
      return new Expression_Apply(expr, args);
    }
    public static _IExpression create_TypeTest(DAST._IExpression @on, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dType, Dafny.ISequence<Dafny.Rune> variant) {
      return new Expression_TypeTest(@on, dType, variant);
    }
    public static _IExpression create_Is(DAST._IExpression expr, DAST._IType fromType, DAST._IType toType) {
      return new Expression_Is(expr, fromType, toType);
    }
    public static _IExpression create_InitializationValue(DAST._IType typ) {
      return new Expression_InitializationValue(typ);
    }
    public static _IExpression create_BoolBoundedPool() {
      return new Expression_BoolBoundedPool();
    }
    public static _IExpression create_SetBoundedPool(DAST._IExpression of) {
      return new Expression_SetBoundedPool(of);
    }
    public static _IExpression create_MapBoundedPool(DAST._IExpression of) {
      return new Expression_MapBoundedPool(of);
    }
    public static _IExpression create_SeqBoundedPool(DAST._IExpression of, bool includeDuplicates) {
      return new Expression_SeqBoundedPool(of, includeDuplicates);
    }
    public static _IExpression create_MultisetBoundedPool(DAST._IExpression of, bool includeDuplicates) {
      return new Expression_MultisetBoundedPool(of, includeDuplicates);
    }
    public static _IExpression create_ExactBoundedPool(DAST._IExpression of) {
      return new Expression_ExactBoundedPool(of);
    }
    public static _IExpression create_IntRange(DAST._IType elemType, DAST._IExpression lo, DAST._IExpression hi, bool up) {
      return new Expression_IntRange(elemType, lo, hi, up);
    }
    public static _IExpression create_UnboundedIntRange(DAST._IExpression start, bool up) {
      return new Expression_UnboundedIntRange(start, up);
    }
    public static _IExpression create_Quantifier(DAST._IType elemType, DAST._IExpression collection, bool is__forall, DAST._IExpression lambda) {
      return new Expression_Quantifier(elemType, collection, is__forall, lambda);
    }
    public bool is_Literal { get { return this is Expression_Literal; } }
    public bool is_Ident { get { return this is Expression_Ident; } }
    public bool is_Companion { get { return this is Expression_Companion; } }
    public bool is_ExternCompanion { get { return this is Expression_ExternCompanion; } }
    public bool is_Tuple { get { return this is Expression_Tuple; } }
    public bool is_New { get { return this is Expression_New; } }
    public bool is_NewUninitArray { get { return this is Expression_NewUninitArray; } }
    public bool is_ArrayIndexToInt { get { return this is Expression_ArrayIndexToInt; } }
    public bool is_FinalizeNewArray { get { return this is Expression_FinalizeNewArray; } }
    public bool is_DatatypeValue { get { return this is Expression_DatatypeValue; } }
    public bool is_Convert { get { return this is Expression_Convert; } }
    public bool is_SeqConstruct { get { return this is Expression_SeqConstruct; } }
    public bool is_SeqValue { get { return this is Expression_SeqValue; } }
    public bool is_SetValue { get { return this is Expression_SetValue; } }
    public bool is_MultisetValue { get { return this is Expression_MultisetValue; } }
    public bool is_MapValue { get { return this is Expression_MapValue; } }
    public bool is_MapBuilder { get { return this is Expression_MapBuilder; } }
    public bool is_SeqUpdate { get { return this is Expression_SeqUpdate; } }
    public bool is_MapUpdate { get { return this is Expression_MapUpdate; } }
    public bool is_SetBuilder { get { return this is Expression_SetBuilder; } }
    public bool is_ToMultiset { get { return this is Expression_ToMultiset; } }
    public bool is_This { get { return this is Expression_This; } }
    public bool is_Ite { get { return this is Expression_Ite; } }
    public bool is_UnOp { get { return this is Expression_UnOp; } }
    public bool is_BinOp { get { return this is Expression_BinOp; } }
    public bool is_ArrayLen { get { return this is Expression_ArrayLen; } }
    public bool is_MapKeys { get { return this is Expression_MapKeys; } }
    public bool is_MapValues { get { return this is Expression_MapValues; } }
    public bool is_MapItems { get { return this is Expression_MapItems; } }
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
    public bool is_Is { get { return this is Expression_Is; } }
    public bool is_InitializationValue { get { return this is Expression_InitializationValue; } }
    public bool is_BoolBoundedPool { get { return this is Expression_BoolBoundedPool; } }
    public bool is_SetBoundedPool { get { return this is Expression_SetBoundedPool; } }
    public bool is_MapBoundedPool { get { return this is Expression_MapBoundedPool; } }
    public bool is_SeqBoundedPool { get { return this is Expression_SeqBoundedPool; } }
    public bool is_MultisetBoundedPool { get { return this is Expression_MultisetBoundedPool; } }
    public bool is_ExactBoundedPool { get { return this is Expression_ExactBoundedPool; } }
    public bool is_IntRange { get { return this is Expression_IntRange; } }
    public bool is_UnboundedIntRange { get { return this is Expression_UnboundedIntRange; } }
    public bool is_Quantifier { get { return this is Expression_Quantifier; } }
    public DAST._ILiteral dtor_Literal_a0 {
      get {
        var d = this;
        return ((Expression_Literal)d)._a0;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        return ((Expression_Ident)d)._name;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_Companion_a0 {
      get {
        var d = this;
        return ((Expression_Companion)d)._a0;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_typeArgs {
      get {
        var d = this;
        if (d is Expression_Companion) { return ((Expression_Companion)d)._typeArgs; }
        if (d is Expression_New) { return ((Expression_New)d)._typeArgs; }
        if (d is Expression_DatatypeValue) { return ((Expression_DatatypeValue)d)._typeArgs; }
        return ((Expression_Call)d)._typeArgs;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_ExternCompanion_a0 {
      get {
        var d = this;
        return ((Expression_ExternCompanion)d)._a0;
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
        return ((Expression_New)d)._path;
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
        return ((Expression_NewUninitArray)d)._dims;
      }
    }
    public DAST._IType dtor_typ {
      get {
        var d = this;
        if (d is Expression_NewUninitArray) { return ((Expression_NewUninitArray)d)._typ; }
        if (d is Expression_FinalizeNewArray) { return ((Expression_FinalizeNewArray)d)._typ; }
        if (d is Expression_Convert) { return ((Expression_Convert)d)._typ; }
        if (d is Expression_SeqValue) { return ((Expression_SeqValue)d)._typ; }
        if (d is Expression_IIFE) { return ((Expression_IIFE)d)._typ; }
        return ((Expression_InitializationValue)d)._typ;
      }
    }
    public DAST._IExpression dtor_value {
      get {
        var d = this;
        if (d is Expression_ArrayIndexToInt) { return ((Expression_ArrayIndexToInt)d)._value; }
        if (d is Expression_FinalizeNewArray) { return ((Expression_FinalizeNewArray)d)._value; }
        if (d is Expression_Convert) { return ((Expression_Convert)d)._value; }
        if (d is Expression_SeqUpdate) { return ((Expression_SeqUpdate)d)._value; }
        if (d is Expression_MapUpdate) { return ((Expression_MapUpdate)d)._value; }
        return ((Expression_IIFE)d)._value;
      }
    }
    public DAST._IResolvedType dtor_datatypeType {
      get {
        var d = this;
        return ((Expression_DatatypeValue)d)._datatypeType;
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
    public DAST._IType dtor_from {
      get {
        var d = this;
        return ((Expression_Convert)d)._from;
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
        if (d is Expression_SetValue) { return ((Expression_SetValue)d)._elements; }
        return ((Expression_MultisetValue)d)._elements;
      }
    }
    public Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> dtor_mapElems {
      get {
        var d = this;
        return ((Expression_MapValue)d)._mapElems;
      }
    }
    public DAST._IType dtor_domainType {
      get {
        var d = this;
        return ((Expression_MapValue)d)._domainType;
      }
    }
    public DAST._IType dtor_rangeType {
      get {
        var d = this;
        return ((Expression_MapValue)d)._rangeType;
      }
    }
    public DAST._IType dtor_keyType {
      get {
        var d = this;
        return ((Expression_MapBuilder)d)._keyType;
      }
    }
    public DAST._IType dtor_valueType {
      get {
        var d = this;
        return ((Expression_MapBuilder)d)._valueType;
      }
    }
    public DAST._IExpression dtor_expr {
      get {
        var d = this;
        if (d is Expression_SeqUpdate) { return ((Expression_SeqUpdate)d)._expr; }
        if (d is Expression_MapUpdate) { return ((Expression_MapUpdate)d)._expr; }
        if (d is Expression_UnOp) { return ((Expression_UnOp)d)._expr; }
        if (d is Expression_ArrayLen) { return ((Expression_ArrayLen)d)._expr; }
        if (d is Expression_MapKeys) { return ((Expression_MapKeys)d)._expr; }
        if (d is Expression_MapValues) { return ((Expression_MapValues)d)._expr; }
        if (d is Expression_MapItems) { return ((Expression_MapItems)d)._expr; }
        if (d is Expression_Select) { return ((Expression_Select)d)._expr; }
        if (d is Expression_SelectFn) { return ((Expression_SelectFn)d)._expr; }
        if (d is Expression_Index) { return ((Expression_Index)d)._expr; }
        if (d is Expression_IndexRange) { return ((Expression_IndexRange)d)._expr; }
        if (d is Expression_TupleSelect) { return ((Expression_TupleSelect)d)._expr; }
        if (d is Expression_BetaRedex) { return ((Expression_BetaRedex)d)._expr; }
        if (d is Expression_Apply) { return ((Expression_Apply)d)._expr; }
        return ((Expression_Is)d)._expr;
      }
    }
    public DAST._IExpression dtor_indexExpr {
      get {
        var d = this;
        if (d is Expression_SeqUpdate) { return ((Expression_SeqUpdate)d)._indexExpr; }
        return ((Expression_MapUpdate)d)._indexExpr;
      }
    }
    public DAST._IType dtor_collectionType {
      get {
        var d = this;
        if (d is Expression_SeqUpdate) { return ((Expression_SeqUpdate)d)._collectionType; }
        return ((Expression_MapUpdate)d)._collectionType;
      }
    }
    public DAST._IType dtor_exprType {
      get {
        var d = this;
        if (d is Expression_SeqUpdate) { return ((Expression_SeqUpdate)d)._exprType; }
        if (d is Expression_MapUpdate) { return ((Expression_MapUpdate)d)._exprType; }
        return ((Expression_ArrayLen)d)._exprType;
      }
    }
    public DAST._IType dtor_elemType {
      get {
        var d = this;
        if (d is Expression_SetBuilder) { return ((Expression_SetBuilder)d)._elemType; }
        if (d is Expression_IntRange) { return ((Expression_IntRange)d)._elemType; }
        return ((Expression_Quantifier)d)._elemType;
      }
    }
    public DAST._IExpression dtor_ToMultiset_a0 {
      get {
        var d = this;
        return ((Expression_ToMultiset)d)._a0;
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
    public DAST.Format._IUnaryOpFormat dtor_format1 {
      get {
        var d = this;
        return ((Expression_UnOp)d)._format1;
      }
    }
    public DAST._ITypedBinOp dtor_op {
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
    public DAST.Format._IBinaryOpFormat dtor_format2 {
      get {
        var d = this;
        return ((Expression_BinOp)d)._format2;
      }
    }
    public BigInteger dtor_dim {
      get {
        var d = this;
        return ((Expression_ArrayLen)d)._dim;
      }
    }
    public bool dtor_native {
      get {
        var d = this;
        return ((Expression_ArrayLen)d)._native;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_field {
      get {
        var d = this;
        if (d is Expression_Select) { return ((Expression_Select)d)._field; }
        return ((Expression_SelectFn)d)._field;
      }
    }
    public DAST._IFieldMutability dtor_fieldMutability {
      get {
        var d = this;
        return ((Expression_Select)d)._fieldMutability;
      }
    }
    public DAST._ISelectContext dtor_selectContext {
      get {
        var d = this;
        return ((Expression_Select)d)._selectContext;
      }
    }
    public DAST._IType dtor_isfieldType {
      get {
        var d = this;
        return ((Expression_Select)d)._isfieldType;
      }
    }
    public bool dtor_onDatatype {
      get {
        var d = this;
        return ((Expression_SelectFn)d)._onDatatype;
      }
    }
    public bool dtor_isStatic {
      get {
        var d = this;
        return ((Expression_SelectFn)d)._isStatic;
      }
    }
    public bool dtor_isConstant {
      get {
        var d = this;
        return ((Expression_SelectFn)d)._isConstant;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_arguments {
      get {
        var d = this;
        return ((Expression_SelectFn)d)._arguments;
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
    public Std.Wrappers._IOption<DAST._IExpression> dtor_low {
      get {
        var d = this;
        return ((Expression_IndexRange)d)._low;
      }
    }
    public Std.Wrappers._IOption<DAST._IExpression> dtor_high {
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
    public DAST._IType dtor_fieldType {
      get {
        var d = this;
        return ((Expression_TupleSelect)d)._fieldType;
      }
    }
    public DAST._IExpression dtor_on {
      get {
        var d = this;
        if (d is Expression_Call) { return ((Expression_Call)d)._on; }
        return ((Expression_TypeTest)d)._on;
      }
    }
    public DAST._ICallName dtor_callName {
      get {
        var d = this;
        return ((Expression_Call)d)._callName;
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
    public Dafny.ISequence<Dafny.Rune> dtor_ident {
      get {
        var d = this;
        return ((Expression_IIFE)d)._ident;
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
    public DAST._IType dtor_fromType {
      get {
        var d = this;
        return ((Expression_Is)d)._fromType;
      }
    }
    public DAST._IType dtor_toType {
      get {
        var d = this;
        return ((Expression_Is)d)._toType;
      }
    }
    public DAST._IExpression dtor_of {
      get {
        var d = this;
        if (d is Expression_SetBoundedPool) { return ((Expression_SetBoundedPool)d)._of; }
        if (d is Expression_MapBoundedPool) { return ((Expression_MapBoundedPool)d)._of; }
        if (d is Expression_SeqBoundedPool) { return ((Expression_SeqBoundedPool)d)._of; }
        if (d is Expression_MultisetBoundedPool) { return ((Expression_MultisetBoundedPool)d)._of; }
        return ((Expression_ExactBoundedPool)d)._of;
      }
    }
    public bool dtor_includeDuplicates {
      get {
        var d = this;
        if (d is Expression_SeqBoundedPool) { return ((Expression_SeqBoundedPool)d)._includeDuplicates; }
        return ((Expression_MultisetBoundedPool)d)._includeDuplicates;
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
    public bool dtor_up {
      get {
        var d = this;
        if (d is Expression_IntRange) { return ((Expression_IntRange)d)._up; }
        return ((Expression_UnboundedIntRange)d)._up;
      }
    }
    public DAST._IExpression dtor_start {
      get {
        var d = this;
        return ((Expression_UnboundedIntRange)d)._start;
      }
    }
    public DAST._IExpression dtor_collection {
      get {
        var d = this;
        return ((Expression_Quantifier)d)._collection;
      }
    }
    public bool dtor_is__forall {
      get {
        var d = this;
        return ((Expression_Quantifier)d)._is__forall;
      }
    }
    public DAST._IExpression dtor_lambda {
      get {
        var d = this;
        return ((Expression_Quantifier)d)._lambda;
      }
    }
    public abstract _IExpression DowncastClone();
    public bool IsThisUpcast() {
      return (((this).is_Convert) && (((this).dtor_value).is_This)) && (((this).dtor_from).Extends((this).dtor_typ));
    }
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
      return (int) hash;
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
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public Expression_Ident(Dafny.ISequence<Dafny.Rune> name) : base() {
      this._name = name;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Ident(_name);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Ident;
      return oth != null && object.Equals(this._name, oth._name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Ident";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ")";
      return s;
    }
  }
  public class Expression_Companion : Expression {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _a0;
    public readonly Dafny.ISequence<DAST._IType> _typeArgs;
    public Expression_Companion(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _a0, Dafny.ISequence<DAST._IType> typeArgs) : base() {
      this._a0 = _a0;
      this._typeArgs = typeArgs;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Companion(_a0, _typeArgs);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Companion;
      return oth != null && object.Equals(this._a0, oth._a0) && object.Equals(this._typeArgs, oth._typeArgs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeArgs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Companion";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeArgs);
      s += ")";
      return s;
    }
  }
  public class Expression_ExternCompanion : Expression {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _a0;
    public Expression_ExternCompanion(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _a0) : base() {
      this._a0 = _a0;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_ExternCompanion(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_ExternCompanion;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.ExternCompanion";
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
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int) hash;
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
    public readonly Dafny.ISequence<DAST._IType> _typeArgs;
    public readonly Dafny.ISequence<DAST._IExpression> _args;
    public Expression_New(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args) : base() {
      this._path = path;
      this._typeArgs = typeArgs;
      this._args = args;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_New(_path, _typeArgs, _args);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_New;
      return oth != null && object.Equals(this._path, oth._path) && object.Equals(this._typeArgs, oth._typeArgs) && object.Equals(this._args, oth._args);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._path));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeArgs));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._args));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.New";
      s += "(";
      s += Dafny.Helpers.ToString(this._path);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeArgs);
      s += ", ";
      s += Dafny.Helpers.ToString(this._args);
      s += ")";
      return s;
    }
  }
  public class Expression_NewUninitArray : Expression {
    public readonly Dafny.ISequence<DAST._IExpression> _dims;
    public readonly DAST._IType _typ;
    public Expression_NewUninitArray(Dafny.ISequence<DAST._IExpression> dims, DAST._IType typ) : base() {
      this._dims = dims;
      this._typ = typ;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_NewUninitArray(_dims, _typ);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_NewUninitArray;
      return oth != null && object.Equals(this._dims, oth._dims) && object.Equals(this._typ, oth._typ);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._dims));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typ));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.NewUninitArray";
      s += "(";
      s += Dafny.Helpers.ToString(this._dims);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typ);
      s += ")";
      return s;
    }
  }
  public class Expression_ArrayIndexToInt : Expression {
    public readonly DAST._IExpression _value;
    public Expression_ArrayIndexToInt(DAST._IExpression @value) : base() {
      this._value = @value;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_ArrayIndexToInt(_value);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_ArrayIndexToInt;
      return oth != null && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.ArrayIndexToInt";
      s += "(";
      s += Dafny.Helpers.ToString(this._value);
      s += ")";
      return s;
    }
  }
  public class Expression_FinalizeNewArray : Expression {
    public readonly DAST._IExpression _value;
    public readonly DAST._IType _typ;
    public Expression_FinalizeNewArray(DAST._IExpression @value, DAST._IType typ) : base() {
      this._value = @value;
      this._typ = typ;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_FinalizeNewArray(_value, _typ);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_FinalizeNewArray;
      return oth != null && object.Equals(this._value, oth._value) && object.Equals(this._typ, oth._typ);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typ));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.FinalizeNewArray";
      s += "(";
      s += Dafny.Helpers.ToString(this._value);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typ);
      s += ")";
      return s;
    }
  }
  public class Expression_DatatypeValue : Expression {
    public readonly DAST._IResolvedType _datatypeType;
    public readonly Dafny.ISequence<DAST._IType> _typeArgs;
    public readonly Dafny.ISequence<Dafny.Rune> _variant;
    public readonly bool _isCo;
    public readonly Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _contents;
    public Expression_DatatypeValue(DAST._IResolvedType datatypeType, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<Dafny.Rune> variant, bool isCo, Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> contents) : base() {
      this._datatypeType = datatypeType;
      this._typeArgs = typeArgs;
      this._variant = variant;
      this._isCo = isCo;
      this._contents = contents;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_DatatypeValue(_datatypeType, _typeArgs, _variant, _isCo, _contents);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_DatatypeValue;
      return oth != null && object.Equals(this._datatypeType, oth._datatypeType) && object.Equals(this._typeArgs, oth._typeArgs) && object.Equals(this._variant, oth._variant) && this._isCo == oth._isCo && object.Equals(this._contents, oth._contents);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._datatypeType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeArgs));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._variant));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._isCo));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._contents));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.DatatypeValue";
      s += "(";
      s += Dafny.Helpers.ToString(this._datatypeType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeArgs);
      s += ", ";
      s += Dafny.Helpers.ToString(this._variant);
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
      hash = ((hash << 5) + hash) + 10;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._from));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typ));
      return (int) hash;
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
      hash = ((hash << 5) + hash) + 11;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._length));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._elem));
      return (int) hash;
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
    public readonly DAST._IType _typ;
    public Expression_SeqValue(Dafny.ISequence<DAST._IExpression> elements, DAST._IType typ) : base() {
      this._elements = elements;
      this._typ = typ;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_SeqValue(_elements, _typ);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_SeqValue;
      return oth != null && object.Equals(this._elements, oth._elements) && object.Equals(this._typ, oth._typ);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 12;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._elements));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typ));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.SeqValue";
      s += "(";
      s += Dafny.Helpers.ToString(this._elements);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typ);
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
      hash = ((hash << 5) + hash) + 13;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._elements));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.SetValue";
      s += "(";
      s += Dafny.Helpers.ToString(this._elements);
      s += ")";
      return s;
    }
  }
  public class Expression_MultisetValue : Expression {
    public readonly Dafny.ISequence<DAST._IExpression> _elements;
    public Expression_MultisetValue(Dafny.ISequence<DAST._IExpression> elements) : base() {
      this._elements = elements;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_MultisetValue(_elements);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_MultisetValue;
      return oth != null && object.Equals(this._elements, oth._elements);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 14;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._elements));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.MultisetValue";
      s += "(";
      s += Dafny.Helpers.ToString(this._elements);
      s += ")";
      return s;
    }
  }
  public class Expression_MapValue : Expression {
    public readonly Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _mapElems;
    public readonly DAST._IType _domainType;
    public readonly DAST._IType _rangeType;
    public Expression_MapValue(Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> mapElems, DAST._IType domainType, DAST._IType rangeType) : base() {
      this._mapElems = mapElems;
      this._domainType = domainType;
      this._rangeType = rangeType;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_MapValue(_mapElems, _domainType, _rangeType);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_MapValue;
      return oth != null && object.Equals(this._mapElems, oth._mapElems) && object.Equals(this._domainType, oth._domainType) && object.Equals(this._rangeType, oth._rangeType);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 15;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._mapElems));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._domainType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._rangeType));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.MapValue";
      s += "(";
      s += Dafny.Helpers.ToString(this._mapElems);
      s += ", ";
      s += Dafny.Helpers.ToString(this._domainType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._rangeType);
      s += ")";
      return s;
    }
  }
  public class Expression_MapBuilder : Expression {
    public readonly DAST._IType _keyType;
    public readonly DAST._IType _valueType;
    public Expression_MapBuilder(DAST._IType keyType, DAST._IType valueType) : base() {
      this._keyType = keyType;
      this._valueType = valueType;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_MapBuilder(_keyType, _valueType);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_MapBuilder;
      return oth != null && object.Equals(this._keyType, oth._keyType) && object.Equals(this._valueType, oth._valueType);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 16;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._valueType));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.MapBuilder";
      s += "(";
      s += Dafny.Helpers.ToString(this._keyType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._valueType);
      s += ")";
      return s;
    }
  }
  public class Expression_SeqUpdate : Expression {
    public readonly DAST._IExpression _expr;
    public readonly DAST._IExpression _indexExpr;
    public readonly DAST._IExpression _value;
    public readonly DAST._IType _collectionType;
    public readonly DAST._IType _exprType;
    public Expression_SeqUpdate(DAST._IExpression expr, DAST._IExpression indexExpr, DAST._IExpression @value, DAST._IType collectionType, DAST._IType exprType) : base() {
      this._expr = expr;
      this._indexExpr = indexExpr;
      this._value = @value;
      this._collectionType = collectionType;
      this._exprType = exprType;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_SeqUpdate(_expr, _indexExpr, _value, _collectionType, _exprType);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_SeqUpdate;
      return oth != null && object.Equals(this._expr, oth._expr) && object.Equals(this._indexExpr, oth._indexExpr) && object.Equals(this._value, oth._value) && object.Equals(this._collectionType, oth._collectionType) && object.Equals(this._exprType, oth._exprType);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 17;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._indexExpr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._collectionType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._exprType));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.SeqUpdate";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._indexExpr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._value);
      s += ", ";
      s += Dafny.Helpers.ToString(this._collectionType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._exprType);
      s += ")";
      return s;
    }
  }
  public class Expression_MapUpdate : Expression {
    public readonly DAST._IExpression _expr;
    public readonly DAST._IExpression _indexExpr;
    public readonly DAST._IExpression _value;
    public readonly DAST._IType _collectionType;
    public readonly DAST._IType _exprType;
    public Expression_MapUpdate(DAST._IExpression expr, DAST._IExpression indexExpr, DAST._IExpression @value, DAST._IType collectionType, DAST._IType exprType) : base() {
      this._expr = expr;
      this._indexExpr = indexExpr;
      this._value = @value;
      this._collectionType = collectionType;
      this._exprType = exprType;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_MapUpdate(_expr, _indexExpr, _value, _collectionType, _exprType);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_MapUpdate;
      return oth != null && object.Equals(this._expr, oth._expr) && object.Equals(this._indexExpr, oth._indexExpr) && object.Equals(this._value, oth._value) && object.Equals(this._collectionType, oth._collectionType) && object.Equals(this._exprType, oth._exprType);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 18;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._indexExpr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._collectionType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._exprType));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.MapUpdate";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._indexExpr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._value);
      s += ", ";
      s += Dafny.Helpers.ToString(this._collectionType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._exprType);
      s += ")";
      return s;
    }
  }
  public class Expression_SetBuilder : Expression {
    public readonly DAST._IType _elemType;
    public Expression_SetBuilder(DAST._IType elemType) : base() {
      this._elemType = elemType;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_SetBuilder(_elemType);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_SetBuilder;
      return oth != null && object.Equals(this._elemType, oth._elemType);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 19;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._elemType));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.SetBuilder";
      s += "(";
      s += Dafny.Helpers.ToString(this._elemType);
      s += ")";
      return s;
    }
  }
  public class Expression_ToMultiset : Expression {
    public readonly DAST._IExpression _a0;
    public Expression_ToMultiset(DAST._IExpression _a0) : base() {
      this._a0 = _a0;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_ToMultiset(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_ToMultiset;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 20;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.ToMultiset";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
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
      hash = ((hash << 5) + hash) + 21;
      return (int) hash;
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
      hash = ((hash << 5) + hash) + 22;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._cond));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._thn));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._els));
      return (int) hash;
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
    public readonly DAST.Format._IUnaryOpFormat _format1;
    public Expression_UnOp(DAST._IUnaryOp unOp, DAST._IExpression expr, DAST.Format._IUnaryOpFormat format1) : base() {
      this._unOp = unOp;
      this._expr = expr;
      this._format1 = format1;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_UnOp(_unOp, _expr, _format1);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_UnOp;
      return oth != null && object.Equals(this._unOp, oth._unOp) && object.Equals(this._expr, oth._expr) && object.Equals(this._format1, oth._format1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 23;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._unOp));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._format1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.UnOp";
      s += "(";
      s += Dafny.Helpers.ToString(this._unOp);
      s += ", ";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._format1);
      s += ")";
      return s;
    }
  }
  public class Expression_BinOp : Expression {
    public readonly DAST._ITypedBinOp _op;
    public readonly DAST._IExpression _left;
    public readonly DAST._IExpression _right;
    public readonly DAST.Format._IBinaryOpFormat _format2;
    public Expression_BinOp(DAST._ITypedBinOp op, DAST._IExpression left, DAST._IExpression right, DAST.Format._IBinaryOpFormat format2) : base() {
      this._op = op;
      this._left = left;
      this._right = right;
      this._format2 = format2;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_BinOp(_op, _left, _right, _format2);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_BinOp;
      return oth != null && object.Equals(this._op, oth._op) && object.Equals(this._left, oth._left) && object.Equals(this._right, oth._right) && object.Equals(this._format2, oth._format2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 24;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._op));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._right));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._format2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.BinOp";
      s += "(";
      s += Dafny.Helpers.ToString(this._op);
      s += ", ";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._right);
      s += ", ";
      s += Dafny.Helpers.ToString(this._format2);
      s += ")";
      return s;
    }
  }
  public class Expression_ArrayLen : Expression {
    public readonly DAST._IExpression _expr;
    public readonly DAST._IType _exprType;
    public readonly BigInteger _dim;
    public readonly bool _native;
    public Expression_ArrayLen(DAST._IExpression expr, DAST._IType exprType, BigInteger dim, bool native) : base() {
      this._expr = expr;
      this._exprType = exprType;
      this._dim = dim;
      this._native = native;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_ArrayLen(_expr, _exprType, _dim, _native);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_ArrayLen;
      return oth != null && object.Equals(this._expr, oth._expr) && object.Equals(this._exprType, oth._exprType) && this._dim == oth._dim && this._native == oth._native;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 25;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._exprType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._dim));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._native));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.ArrayLen";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._exprType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._dim);
      s += ", ";
      s += Dafny.Helpers.ToString(this._native);
      s += ")";
      return s;
    }
  }
  public class Expression_MapKeys : Expression {
    public readonly DAST._IExpression _expr;
    public Expression_MapKeys(DAST._IExpression expr) : base() {
      this._expr = expr;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_MapKeys(_expr);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_MapKeys;
      return oth != null && object.Equals(this._expr, oth._expr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 26;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.MapKeys";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ")";
      return s;
    }
  }
  public class Expression_MapValues : Expression {
    public readonly DAST._IExpression _expr;
    public Expression_MapValues(DAST._IExpression expr) : base() {
      this._expr = expr;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_MapValues(_expr);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_MapValues;
      return oth != null && object.Equals(this._expr, oth._expr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 27;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.MapValues";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ")";
      return s;
    }
  }
  public class Expression_MapItems : Expression {
    public readonly DAST._IExpression _expr;
    public Expression_MapItems(DAST._IExpression expr) : base() {
      this._expr = expr;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_MapItems(_expr);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_MapItems;
      return oth != null && object.Equals(this._expr, oth._expr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 28;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.MapItems";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ")";
      return s;
    }
  }
  public class Expression_Select : Expression {
    public readonly DAST._IExpression _expr;
    public readonly Dafny.ISequence<Dafny.Rune> _field;
    public readonly DAST._IFieldMutability _fieldMutability;
    public readonly DAST._ISelectContext _selectContext;
    public readonly DAST._IType _isfieldType;
    public Expression_Select(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, DAST._IFieldMutability fieldMutability, DAST._ISelectContext selectContext, DAST._IType isfieldType) : base() {
      this._expr = expr;
      this._field = field;
      this._fieldMutability = fieldMutability;
      this._selectContext = selectContext;
      this._isfieldType = isfieldType;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Select(_expr, _field, _fieldMutability, _selectContext, _isfieldType);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Select;
      return oth != null && object.Equals(this._expr, oth._expr) && object.Equals(this._field, oth._field) && object.Equals(this._fieldMutability, oth._fieldMutability) && object.Equals(this._selectContext, oth._selectContext) && object.Equals(this._isfieldType, oth._isfieldType);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 29;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._field));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fieldMutability));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._selectContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._isfieldType));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Select";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._field);
      s += ", ";
      s += Dafny.Helpers.ToString(this._fieldMutability);
      s += ", ";
      s += Dafny.Helpers.ToString(this._selectContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this._isfieldType);
      s += ")";
      return s;
    }
  }
  public class Expression_SelectFn : Expression {
    public readonly DAST._IExpression _expr;
    public readonly Dafny.ISequence<Dafny.Rune> _field;
    public readonly bool _onDatatype;
    public readonly bool _isStatic;
    public readonly bool _isConstant;
    public readonly Dafny.ISequence<DAST._IType> _arguments;
    public Expression_SelectFn(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, bool onDatatype, bool isStatic, bool isConstant, Dafny.ISequence<DAST._IType> arguments) : base() {
      this._expr = expr;
      this._field = field;
      this._onDatatype = onDatatype;
      this._isStatic = isStatic;
      this._isConstant = isConstant;
      this._arguments = arguments;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_SelectFn(_expr, _field, _onDatatype, _isStatic, _isConstant, _arguments);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_SelectFn;
      return oth != null && object.Equals(this._expr, oth._expr) && object.Equals(this._field, oth._field) && this._onDatatype == oth._onDatatype && this._isStatic == oth._isStatic && this._isConstant == oth._isConstant && object.Equals(this._arguments, oth._arguments);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 30;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._field));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._onDatatype));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._isStatic));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._isConstant));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._arguments));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.SelectFn";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._field);
      s += ", ";
      s += Dafny.Helpers.ToString(this._onDatatype);
      s += ", ";
      s += Dafny.Helpers.ToString(this._isStatic);
      s += ", ";
      s += Dafny.Helpers.ToString(this._isConstant);
      s += ", ";
      s += Dafny.Helpers.ToString(this._arguments);
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
      hash = ((hash << 5) + hash) + 31;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._collKind));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._indices));
      return (int) hash;
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
    public readonly Std.Wrappers._IOption<DAST._IExpression> _low;
    public readonly Std.Wrappers._IOption<DAST._IExpression> _high;
    public Expression_IndexRange(DAST._IExpression expr, bool isArray, Std.Wrappers._IOption<DAST._IExpression> low, Std.Wrappers._IOption<DAST._IExpression> high) : base() {
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
      hash = ((hash << 5) + hash) + 32;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._isArray));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._low));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._high));
      return (int) hash;
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
    public readonly DAST._IType _fieldType;
    public Expression_TupleSelect(DAST._IExpression expr, BigInteger index, DAST._IType fieldType) : base() {
      this._expr = expr;
      this._index = index;
      this._fieldType = fieldType;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_TupleSelect(_expr, _index, _fieldType);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_TupleSelect;
      return oth != null && object.Equals(this._expr, oth._expr) && this._index == oth._index && object.Equals(this._fieldType, oth._fieldType);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 33;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._index));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fieldType));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.TupleSelect";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._index);
      s += ", ";
      s += Dafny.Helpers.ToString(this._fieldType);
      s += ")";
      return s;
    }
  }
  public class Expression_Call : Expression {
    public readonly DAST._IExpression _on;
    public readonly DAST._ICallName _callName;
    public readonly Dafny.ISequence<DAST._IType> _typeArgs;
    public readonly Dafny.ISequence<DAST._IExpression> _args;
    public Expression_Call(DAST._IExpression @on, DAST._ICallName callName, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args) : base() {
      this._on = @on;
      this._callName = callName;
      this._typeArgs = typeArgs;
      this._args = args;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Call(_on, _callName, _typeArgs, _args);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Call;
      return oth != null && object.Equals(this._on, oth._on) && object.Equals(this._callName, oth._callName) && object.Equals(this._typeArgs, oth._typeArgs) && object.Equals(this._args, oth._args);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 34;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._on));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._callName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeArgs));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._args));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Call";
      s += "(";
      s += Dafny.Helpers.ToString(this._on);
      s += ", ";
      s += Dafny.Helpers.ToString(this._callName);
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
      hash = ((hash << 5) + hash) + 35;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._params));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._retType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int) hash;
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
      hash = ((hash << 5) + hash) + 36;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._values));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._retType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      return (int) hash;
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
    public readonly Dafny.ISequence<Dafny.Rune> _ident;
    public readonly DAST._IType _typ;
    public readonly DAST._IExpression _value;
    public readonly DAST._IExpression _iifeBody;
    public Expression_IIFE(Dafny.ISequence<Dafny.Rune> ident, DAST._IType typ, DAST._IExpression @value, DAST._IExpression iifeBody) : base() {
      this._ident = ident;
      this._typ = typ;
      this._value = @value;
      this._iifeBody = iifeBody;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_IIFE(_ident, _typ, _value, _iifeBody);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_IIFE;
      return oth != null && object.Equals(this._ident, oth._ident) && object.Equals(this._typ, oth._typ) && object.Equals(this._value, oth._value) && object.Equals(this._iifeBody, oth._iifeBody);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 37;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ident));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typ));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._iifeBody));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.IIFE";
      s += "(";
      s += Dafny.Helpers.ToString(this._ident);
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
      hash = ((hash << 5) + hash) + 38;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._args));
      return (int) hash;
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
      hash = ((hash << 5) + hash) + 39;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._on));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._dType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._variant));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.TypeTest";
      s += "(";
      s += Dafny.Helpers.ToString(this._on);
      s += ", ";
      s += Dafny.Helpers.ToString(this._dType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._variant);
      s += ")";
      return s;
    }
  }
  public class Expression_Is : Expression {
    public readonly DAST._IExpression _expr;
    public readonly DAST._IType _fromType;
    public readonly DAST._IType _toType;
    public Expression_Is(DAST._IExpression expr, DAST._IType fromType, DAST._IType toType) : base() {
      this._expr = expr;
      this._fromType = fromType;
      this._toType = toType;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Is(_expr, _fromType, _toType);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Is;
      return oth != null && object.Equals(this._expr, oth._expr) && object.Equals(this._fromType, oth._fromType) && object.Equals(this._toType, oth._toType);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 40;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fromType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._toType));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Is";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._fromType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._toType);
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
      hash = ((hash << 5) + hash) + 41;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typ));
      return (int) hash;
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
      hash = ((hash << 5) + hash) + 42;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.BoolBoundedPool";
      return s;
    }
  }
  public class Expression_SetBoundedPool : Expression {
    public readonly DAST._IExpression _of;
    public Expression_SetBoundedPool(DAST._IExpression of) : base() {
      this._of = of;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_SetBoundedPool(_of);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_SetBoundedPool;
      return oth != null && object.Equals(this._of, oth._of);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 43;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._of));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.SetBoundedPool";
      s += "(";
      s += Dafny.Helpers.ToString(this._of);
      s += ")";
      return s;
    }
  }
  public class Expression_MapBoundedPool : Expression {
    public readonly DAST._IExpression _of;
    public Expression_MapBoundedPool(DAST._IExpression of) : base() {
      this._of = of;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_MapBoundedPool(_of);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_MapBoundedPool;
      return oth != null && object.Equals(this._of, oth._of);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 44;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._of));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.MapBoundedPool";
      s += "(";
      s += Dafny.Helpers.ToString(this._of);
      s += ")";
      return s;
    }
  }
  public class Expression_SeqBoundedPool : Expression {
    public readonly DAST._IExpression _of;
    public readonly bool _includeDuplicates;
    public Expression_SeqBoundedPool(DAST._IExpression of, bool includeDuplicates) : base() {
      this._of = of;
      this._includeDuplicates = includeDuplicates;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_SeqBoundedPool(_of, _includeDuplicates);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_SeqBoundedPool;
      return oth != null && object.Equals(this._of, oth._of) && this._includeDuplicates == oth._includeDuplicates;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 45;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._of));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._includeDuplicates));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.SeqBoundedPool";
      s += "(";
      s += Dafny.Helpers.ToString(this._of);
      s += ", ";
      s += Dafny.Helpers.ToString(this._includeDuplicates);
      s += ")";
      return s;
    }
  }
  public class Expression_MultisetBoundedPool : Expression {
    public readonly DAST._IExpression _of;
    public readonly bool _includeDuplicates;
    public Expression_MultisetBoundedPool(DAST._IExpression of, bool includeDuplicates) : base() {
      this._of = of;
      this._includeDuplicates = includeDuplicates;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_MultisetBoundedPool(_of, _includeDuplicates);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_MultisetBoundedPool;
      return oth != null && object.Equals(this._of, oth._of) && this._includeDuplicates == oth._includeDuplicates;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 46;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._of));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._includeDuplicates));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.MultisetBoundedPool";
      s += "(";
      s += Dafny.Helpers.ToString(this._of);
      s += ", ";
      s += Dafny.Helpers.ToString(this._includeDuplicates);
      s += ")";
      return s;
    }
  }
  public class Expression_ExactBoundedPool : Expression {
    public readonly DAST._IExpression _of;
    public Expression_ExactBoundedPool(DAST._IExpression of) : base() {
      this._of = of;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_ExactBoundedPool(_of);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_ExactBoundedPool;
      return oth != null && object.Equals(this._of, oth._of);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 47;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._of));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.ExactBoundedPool";
      s += "(";
      s += Dafny.Helpers.ToString(this._of);
      s += ")";
      return s;
    }
  }
  public class Expression_IntRange : Expression {
    public readonly DAST._IType _elemType;
    public readonly DAST._IExpression _lo;
    public readonly DAST._IExpression _hi;
    public readonly bool _up;
    public Expression_IntRange(DAST._IType elemType, DAST._IExpression lo, DAST._IExpression hi, bool up) : base() {
      this._elemType = elemType;
      this._lo = lo;
      this._hi = hi;
      this._up = up;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_IntRange(_elemType, _lo, _hi, _up);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_IntRange;
      return oth != null && object.Equals(this._elemType, oth._elemType) && object.Equals(this._lo, oth._lo) && object.Equals(this._hi, oth._hi) && this._up == oth._up;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 48;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._elemType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._lo));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._hi));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._up));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.IntRange";
      s += "(";
      s += Dafny.Helpers.ToString(this._elemType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._lo);
      s += ", ";
      s += Dafny.Helpers.ToString(this._hi);
      s += ", ";
      s += Dafny.Helpers.ToString(this._up);
      s += ")";
      return s;
    }
  }
  public class Expression_UnboundedIntRange : Expression {
    public readonly DAST._IExpression _start;
    public readonly bool _up;
    public Expression_UnboundedIntRange(DAST._IExpression start, bool up) : base() {
      this._start = start;
      this._up = up;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_UnboundedIntRange(_start, _up);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_UnboundedIntRange;
      return oth != null && object.Equals(this._start, oth._start) && this._up == oth._up;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 49;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._start));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._up));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.UnboundedIntRange";
      s += "(";
      s += Dafny.Helpers.ToString(this._start);
      s += ", ";
      s += Dafny.Helpers.ToString(this._up);
      s += ")";
      return s;
    }
  }
  public class Expression_Quantifier : Expression {
    public readonly DAST._IType _elemType;
    public readonly DAST._IExpression _collection;
    public readonly bool _is__forall;
    public readonly DAST._IExpression _lambda;
    public Expression_Quantifier(DAST._IType elemType, DAST._IExpression collection, bool is__forall, DAST._IExpression lambda) : base() {
      this._elemType = elemType;
      this._collection = collection;
      this._is__forall = is__forall;
      this._lambda = lambda;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Quantifier(_elemType, _collection, _is__forall, _lambda);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Quantifier;
      return oth != null && object.Equals(this._elemType, oth._elemType) && object.Equals(this._collection, oth._collection) && this._is__forall == oth._is__forall && object.Equals(this._lambda, oth._lambda);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 50;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._elemType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._collection));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._is__forall));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._lambda));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Quantifier";
      s += "(";
      s += Dafny.Helpers.ToString(this._elemType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._collection);
      s += ", ";
      s += Dafny.Helpers.ToString(this._is__forall);
      s += ", ";
      s += Dafny.Helpers.ToString(this._lambda);
      s += ")";
      return s;
    }
  }

  public interface _IFieldMutability {
    bool is_ConstantField { get; }
    bool is_InternalClassConstantFieldOrDatatypeDestructor { get; }
    bool is_ClassMutableField { get; }
    _IFieldMutability DowncastClone();
  }
  public abstract class FieldMutability : _IFieldMutability {
    public FieldMutability() {
    }
    private static readonly DAST._IFieldMutability theDefault = create_ConstantField();
    public static DAST._IFieldMutability Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IFieldMutability> _TYPE = new Dafny.TypeDescriptor<DAST._IFieldMutability>(DAST.FieldMutability.Default());
    public static Dafny.TypeDescriptor<DAST._IFieldMutability> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IFieldMutability create_ConstantField() {
      return new FieldMutability_ConstantField();
    }
    public static _IFieldMutability create_InternalClassConstantFieldOrDatatypeDestructor() {
      return new FieldMutability_InternalClassConstantFieldOrDatatypeDestructor();
    }
    public static _IFieldMutability create_ClassMutableField() {
      return new FieldMutability_ClassMutableField();
    }
    public bool is_ConstantField { get { return this is FieldMutability_ConstantField; } }
    public bool is_InternalClassConstantFieldOrDatatypeDestructor { get { return this is FieldMutability_InternalClassConstantFieldOrDatatypeDestructor; } }
    public bool is_ClassMutableField { get { return this is FieldMutability_ClassMutableField; } }
    public static System.Collections.Generic.IEnumerable<_IFieldMutability> AllSingletonConstructors {
      get {
        yield return FieldMutability.create_ConstantField();
        yield return FieldMutability.create_InternalClassConstantFieldOrDatatypeDestructor();
        yield return FieldMutability.create_ClassMutableField();
      }
    }
    public abstract _IFieldMutability DowncastClone();
  }
  public class FieldMutability_ConstantField : FieldMutability {
    public FieldMutability_ConstantField() : base() {
    }
    public override _IFieldMutability DowncastClone() {
      if (this is _IFieldMutability dt) { return dt; }
      return new FieldMutability_ConstantField();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.FieldMutability_ConstantField;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.FieldMutability.ConstantField";
      return s;
    }
  }
  public class FieldMutability_InternalClassConstantFieldOrDatatypeDestructor : FieldMutability {
    public FieldMutability_InternalClassConstantFieldOrDatatypeDestructor() : base() {
    }
    public override _IFieldMutability DowncastClone() {
      if (this is _IFieldMutability dt) { return dt; }
      return new FieldMutability_InternalClassConstantFieldOrDatatypeDestructor();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.FieldMutability_InternalClassConstantFieldOrDatatypeDestructor;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.FieldMutability.InternalClassConstantFieldOrDatatypeDestructor";
      return s;
    }
  }
  public class FieldMutability_ClassMutableField : FieldMutability {
    public FieldMutability_ClassMutableField() : base() {
    }
    public override _IFieldMutability DowncastClone() {
      if (this is _IFieldMutability dt) { return dt; }
      return new FieldMutability_ClassMutableField();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.FieldMutability_ClassMutableField;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.FieldMutability.ClassMutableField";
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
      return (int) hash;
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
      return (int) hash;
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
      return (int) hash;
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
    bool is_CharLiteralUTF16 { get; }
    bool is_Null { get; }
    bool dtor_BoolLiteral_a0 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_IntLiteral_a0 { get; }
    DAST._IType dtor_IntLiteral_a1 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_DecLiteral_a0 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_DecLiteral_a1 { get; }
    DAST._IType dtor_DecLiteral_a2 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_StringLiteral_a0 { get; }
    bool dtor_verbatim { get; }
    Dafny.Rune dtor_CharLiteral_a0 { get; }
    BigInteger dtor_CharLiteralUTF16_a0 { get; }
    DAST._IType dtor_Null_a0 { get; }
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
    public static _ILiteral create_StringLiteral(Dafny.ISequence<Dafny.Rune> _a0, bool verbatim) {
      return new Literal_StringLiteral(_a0, verbatim);
    }
    public static _ILiteral create_CharLiteral(Dafny.Rune _a0) {
      return new Literal_CharLiteral(_a0);
    }
    public static _ILiteral create_CharLiteralUTF16(BigInteger _a0) {
      return new Literal_CharLiteralUTF16(_a0);
    }
    public static _ILiteral create_Null(DAST._IType _a0) {
      return new Literal_Null(_a0);
    }
    public bool is_BoolLiteral { get { return this is Literal_BoolLiteral; } }
    public bool is_IntLiteral { get { return this is Literal_IntLiteral; } }
    public bool is_DecLiteral { get { return this is Literal_DecLiteral; } }
    public bool is_StringLiteral { get { return this is Literal_StringLiteral; } }
    public bool is_CharLiteral { get { return this is Literal_CharLiteral; } }
    public bool is_CharLiteralUTF16 { get { return this is Literal_CharLiteralUTF16; } }
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
    public bool dtor_verbatim {
      get {
        var d = this;
        return ((Literal_StringLiteral)d)._verbatim;
      }
    }
    public Dafny.Rune dtor_CharLiteral_a0 {
      get {
        var d = this;
        return ((Literal_CharLiteral)d)._a0;
      }
    }
    public BigInteger dtor_CharLiteralUTF16_a0 {
      get {
        var d = this;
        return ((Literal_CharLiteralUTF16)d)._a0;
      }
    }
    public DAST._IType dtor_Null_a0 {
      get {
        var d = this;
        return ((Literal_Null)d)._a0;
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
      return (int) hash;
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
      return (int) hash;
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
      return (int) hash;
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
    public readonly bool _verbatim;
    public Literal_StringLiteral(Dafny.ISequence<Dafny.Rune> _a0, bool verbatim) : base() {
      this._a0 = _a0;
      this._verbatim = verbatim;
    }
    public override _ILiteral DowncastClone() {
      if (this is _ILiteral dt) { return dt; }
      return new Literal_StringLiteral(_a0, _verbatim);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Literal_StringLiteral;
      return oth != null && object.Equals(this._a0, oth._a0) && this._verbatim == oth._verbatim;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._verbatim));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Literal.StringLiteral";
      s += "(";
      s += this._a0.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._verbatim);
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
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Literal.CharLiteral";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class Literal_CharLiteralUTF16 : Literal {
    public readonly BigInteger _a0;
    public Literal_CharLiteralUTF16(BigInteger _a0) : base() {
      this._a0 = _a0;
    }
    public override _ILiteral DowncastClone() {
      if (this is _ILiteral dt) { return dt; }
      return new Literal_CharLiteralUTF16(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Literal_CharLiteralUTF16;
      return oth != null && this._a0 == oth._a0;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Literal.CharLiteralUTF16";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class Literal_Null : Literal {
    public readonly DAST._IType _a0;
    public Literal_Null(DAST._IType _a0) : base() {
      this._a0 = _a0;
    }
    public override _ILiteral DowncastClone() {
      if (this is _ILiteral dt) { return dt; }
      return new Literal_Null(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Literal_Null;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Literal.Null";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
} // end of namespace DAST