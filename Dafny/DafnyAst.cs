//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Text;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Numerics;
using Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class Program {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Name != null);
      Contract.Invariant(cce.NonNullElements(Modules));
    }

    public readonly string Name;
    public readonly List<ModuleDecl/*!*/>/*!*/ Modules;
    public readonly BuiltIns BuiltIns;
    public Program(string name, [Captured] List<ModuleDecl/*!*/>/*!*/ modules, [Captured] BuiltIns builtIns) {
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(modules));
      Name = name;
      Modules = modules;
      BuiltIns = builtIns;
    }
  }

  public class BuiltIns
  {
    public readonly ModuleDecl SystemModule = new ModuleDecl(Token.NoToken, "_System", new List<string>(), null);
    Dictionary<int, ClassDecl/*!*/> arrayTypeDecls = new Dictionary<int, ClassDecl>();

    public BuiltIns() {
      // create class 'object'
      ClassDecl obj = new ClassDecl(Token.NoToken, "object", SystemModule, new List<TypeParameter>(), new List<MemberDecl>(), null);
      SystemModule.TopLevelDecls.Add(obj);
      // add one-dimensional arrays, since they may arise during type checking
      UserDefinedType tmp = ArrayType(Token.NoToken, 1, Type.Int, true);
    }

    public UserDefinedType ArrayType(int dims, Type arg) {
      return ArrayType(Token.NoToken, dims, arg, false);
    }
    public UserDefinedType ArrayType(IToken tok, int dims, Type arg, bool allowCreationOfNewClass) {
      Contract.Requires(tok != null);
      Contract.Requires(1 <= dims);
      Contract.Requires(arg != null);
      Contract.Ensures(Contract.Result<UserDefinedType>() != null);

      List<Type/*!*/> typeArgs = new List<Type/*!*/>();
      typeArgs.Add(arg);
      UserDefinedType udt = new UserDefinedType(tok, ArrayClassName(dims), typeArgs);
      if (allowCreationOfNewClass && !arrayTypeDecls.ContainsKey(dims)) {
        ArrayClassDecl arrayClass = new ArrayClassDecl(dims, SystemModule);
        for (int d = 0; d < dims; d++) {
          string name = dims == 1 ? "Length" : "Length" + d;
          string compiledName = dims == 1 ? "Length" : "GetLength(" + d + ")";
          Field len = new SpecialField(Token.NoToken, name, compiledName, "new BigInteger(", ")", false, false, Type.Int, null);
          len.EnclosingClass = arrayClass;  // resolve here
          arrayClass.Members.Add(len);
        }
        arrayTypeDecls.Add(dims, arrayClass);
        SystemModule.TopLevelDecls.Add(arrayClass);
      }
      udt.ResolvedClass = arrayTypeDecls[dims];
      return udt;
    }

    public static string ArrayClassName(int dims) {
      Contract.Requires(1 <= dims);
      if (dims == 1) {
        return "array";
      } else {
        return "array" + dims;
      }
    }
  }

  public class Attributes {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Name != null);
      Contract.Invariant(cce.NonNullElements(Args));
    }

    public readonly string Name;
    /*Frozen*/
    public readonly List<Argument/*!*/>/*!*/ Args;
    public readonly Attributes Prev;

    public Attributes(string name, [Captured] List<Argument/*!*/>/*!*/ args, Attributes prev) {
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(args));
      Name = name;
      Args = args;
      Prev = prev;
    }

    public class Argument {
      public readonly string S;
      public readonly Expression E;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant((S == null) != (E == null));
      }

      public Argument(string s) {
        Contract.Requires(s != null);
        S = s;
      }
      public Argument(Expression e) {
        Contract.Requires(e != null);
        E = e;
      }
    }
  }

  // ------------------------------------------------------------------------------------------------------

  public abstract class Type {
    public static readonly BoolType Bool = new BoolType();
    public static readonly IntType Int = new IntType();
    /// <summary>
    /// Used in error situations in order to reduce further error messages.
    /// </summary>
    //[Pure(false)]
    public static Type Flexible {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);
        return new InferredTypeProxy();
      }
    }

    /// <summary>
    /// Return the most constrained version of "this".
    /// </summary>
    /// <returns></returns>
    public Type Normalize() {
      Contract.Ensures(Contract.Result<Type>() != null);
      Type type = this;
      while (true) {
        TypeProxy pt = type as TypeProxy;
        if (pt != null && pt.T != null) {
          type = pt.T;
        } else {
          return type;
        }
      }
    }

    public bool IsSubrangeType {
      get { return this is NatType; }
    }

    public bool IsRefType {
      get {
        if (this is ObjectType) {
          return true;
        } else {
          UserDefinedType udt = this as UserDefinedType;
          return udt != null && udt.ResolvedParam == null && !(udt.ResolvedClass is DatatypeDecl);
        }
      }
    }
    public bool IsArrayType {
      get {
        return AsArrayType != null;
      }
    }
    public ArrayClassDecl/*?*/ AsArrayType {
      get {
        UserDefinedType udt = UserDefinedType.DenotesClass(this);
        return udt == null ? null : udt.ResolvedClass as ArrayClassDecl;
      }
    }
    public bool IsDatatype {
      get {
        return AsDatatype != null;
      }
    }
    public DatatypeDecl AsDatatype {
      get {
        UserDefinedType udt = this as UserDefinedType;
        if (udt == null) {
          return null;
        } else {
          return udt.ResolvedClass as DatatypeDecl;
        }
      }
    }
    public bool IsTypeParameter {
      get {
        Contract.Ensures(!Contract.Result<bool>() || this is UserDefinedType && ((UserDefinedType)this).ResolvedParam != null);
        UserDefinedType ct = this as UserDefinedType;
        return ct != null && ct.ResolvedParam != null;
      }
    }
  }

  /// <summary>
  /// A NonProxy type is a fully constrained type.  It may contain members.
  /// </summary>
  public abstract class NonProxyType : Type
  {
  }

  public abstract class BasicType : NonProxyType
  {
  }

  public class BoolType : BasicType {
    [Pure]
    public override string ToString() {
      return "bool";
    }
  }

  public class IntType : BasicType {
    [Pure]
    public override string ToString() {
      return "int";
    }
  }

  public class NatType : IntType
  {
    [Pure]
    public override string ToString() {
      return "nat";
    }
  }

  public class ObjectType : BasicType
  {
    [Pure]
    public override string ToString() {
      return "object";
    }
  }

  public abstract class CollectionType : NonProxyType
  {
    public readonly Type Arg;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Arg != null);
    }

    public CollectionType(Type arg) {
      Contract.Requires(arg != null);
      this.Arg = arg;
    }
  }

  public class SetType : CollectionType {
    public SetType(Type arg) : base(arg) {
      Contract.Requires(arg != null);
    }
    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(cce.IsPeerConsistent(Arg));
      return "set<" + base.Arg + ">";
    }
  }

  public class SeqType : CollectionType {
    public SeqType(Type arg) : base(arg) {
      Contract.Requires(arg != null);

    }
    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(cce.IsPeerConsistent(Arg));
      return "seq<" + base.Arg + ">";
    }
  }

  public class UserDefinedType : NonProxyType
  {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
      Contract.Invariant(Name != null);
      Contract.Invariant(cce.NonNullElements(TypeArgs));
    }

    public readonly IToken tok;
    public readonly string Name;
    [Rep]
    public readonly List<Type/*!*/>/*!*/ TypeArgs;

    public TopLevelDecl ResolvedClass;  // filled in by resolution, if Name denotes a class/datatype and TypeArgs match the type parameters of that class/datatype
    public TypeParameter ResolvedParam;  // filled in by resolution, if Name denotes an enclosing type parameter and TypeArgs is the empty list

    public UserDefinedType(IToken/*!*/ tok, string/*!*/ name, [Captured] List<Type/*!*/>/*!*/ typeArgs) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(typeArgs != null);
      this.tok = tok;
      this.Name = name;
      this.TypeArgs = typeArgs;
    }

    /// <summary>
    /// This constructor constructs a resolved class type
    /// </summary>
    public UserDefinedType(IToken/*!*/ tok, string/*!*/ name, TopLevelDecl/*!*/ cd, [Captured] List<Type/*!*/>/*!*/ typeArgs) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cd != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      this.tok = tok;
      this.Name = name;
      this.TypeArgs = typeArgs;
      this.ResolvedClass = cd;
    }

    /// <summary>
    /// This constructor constructs a resolved type parameter
    /// </summary>
    public UserDefinedType(IToken/*!*/ tok, string/*!*/ name, TypeParameter/*!*/ tp) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(tp != null);
      this.tok = tok;
      this.Name = name;
      this.TypeArgs = new List<Type/*!*/>();
      this.ResolvedParam = tp;
    }

    /// <summary>
    /// If type denotes a resolved class type, then return that class type.
    /// Otherwise, return null.
    /// </summary>
    public static UserDefinedType DenotesClass(Type/*!*/ type) {
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<UserDefinedType>() == null || Contract.Result<UserDefinedType>().ResolvedClass is ClassDecl);
      type = type.Normalize();
      UserDefinedType ct = type as UserDefinedType;
      if (ct != null && ct.ResolvedClass is ClassDecl) {
        return ct;
      } else {
        return null;
      }
    }

    public static Type ArrayElementType(Type type) {
      Contract.Requires(type.IsArrayType);

      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<Type>() != null);

      UserDefinedType udt = DenotesClass(type);
      Contract.Assert(udt != null);
      Contract.Assert(udt.TypeArgs.Count == 1);  // holds true of all array types
      return udt.TypeArgs[0];
    }

    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);

      string s = Name;
      if (TypeArgs.Count != 0) {
        string sep = "<";
        foreach (Type t in TypeArgs) {
          Contract.Assume(cce.IsPeerConsistent(t));
          s += sep + t;
          sep = ",";
        }
        s += ">";
      }
      return s;
    }
  }

  public abstract class TypeProxy : Type {
    public Type T;  // filled in during resolution
    internal TypeProxy() {
    }

    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);

      Contract.Assume(T == null || cce.IsPeerConsistent(T));
      return T == null ? "?" : T.ToString();
    }
  }

  public abstract class UnrestrictedTypeProxy : TypeProxy {
  }

  /// <summary>
  /// This proxy stands for any type.
  /// </summary>  
  public class InferredTypeProxy : UnrestrictedTypeProxy {
  }

  /// <summary>
  /// This proxy stands for any type, but it originates from an instantiated type parameter.
  /// </summary>  
  public class ParamTypeProxy : UnrestrictedTypeProxy {
    TypeParameter orig;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(orig != null);
    }

    public ParamTypeProxy(TypeParameter orig) {
      Contract.Requires(orig != null);
      this.orig = orig;
    }
  }

  public abstract class RestrictedTypeProxy : TypeProxy {
    /// <summary>
    /// The OrderID is used to simplify the unification code.  Each restricted type proxy should use its
    /// own OrderID.
    /// </summary>
    public abstract int OrderID {
      get;
    }
  }

  /// <summary>
  /// This proxy stands for any datatype.
  /// </summary>  
  public class DatatypeProxy : RestrictedTypeProxy {
    public override int OrderID {
      get {
        return 0;
      }
    }
  }

  /// <summary>
  /// This proxy stands for object or any class/array type.
  /// </summary>  
  public class ObjectTypeProxy : RestrictedTypeProxy {
    public override int OrderID {
      get {
        return 1;
      }
    }
  }

  /// <summary>
  /// This proxy stands for object or any class/array type or a set/sequence of object or a class/array type.
  /// </summary>
  public class ObjectsTypeProxy : RestrictedTypeProxy {
    public override int OrderID {
      get {
        return 2;
      }
    }
  }

  /// <summary>
  /// This proxy stands for:
  ///     set(Arg) or seq(Arg)
  /// </summary>
  public class CollectionTypeProxy : RestrictedTypeProxy {
    public readonly Type Arg;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Arg != null);
    }

    public CollectionTypeProxy(Type arg) {
      Contract.Requires(arg != null);
      Arg = arg;
    }
    public override int OrderID {
      get {
        return 3;
      }
    }
  }

  /// <summary>
  /// This proxy stands for either:
  ///     int or set or seq
  /// if AllowSeq, or:
  ///     int or set
  /// if !AllowSeq.
  /// </summary>  
  public class OperationTypeProxy : RestrictedTypeProxy {
    public readonly bool AllowSeq;
    public OperationTypeProxy(bool allowSeq) {
      AllowSeq = allowSeq;
    }
    public override int OrderID {
      get {
        return 4;
      }
    }
  }

  /// <summary>
  /// This proxy stands for:
  ///     seq(Arg) or array(Arg)
  /// </summary>
  public class IndexableTypeProxy : RestrictedTypeProxy {
    public readonly Type Arg;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Arg != null);
    }

    public IndexableTypeProxy(Type arg) {
      Contract.Requires(arg != null);
      Arg = arg;
    }
    public override int OrderID {
      get {
        return 5;
      }
    }
  }

  // ------------------------------------------------------------------------------------------------------

  public abstract class Declaration {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
      Contract.Invariant(Name != null);
    }

    public IToken/*!*/ tok;
    public IToken BodyStartTok = Token.NoToken;
    public IToken BodyEndTok = Token.NoToken;
    public readonly string/*!*/ Name;
    public readonly Attributes Attributes;

    public Declaration(IToken tok, string name, Attributes attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      this.tok = tok;
      this.Name = name;
      this.Attributes = attributes;
    }

    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);

      return Name;
    }
  }

  public class TypeParameter : Declaration {
    public interface ParentType {
    }
    [Peer]
    ParentType parent;
    public ParentType Parent {
      get {
        return parent;
      }
      [param: Captured]
      set {
        Contract.Requires(Parent == null);  // set it only once
        Contract.Requires(value != null);
        // BUGBUG:  The following line is a workaround to tell the verifier that 'value' is not of an Immutable type.
        // A proper solution would be to be able to express that in the program (in a specification or attribute) or
        // to be able to declare 'parent' as [PeerOrImmutable].
        Contract.Requires(value is TopLevelDecl || value is Function || value is Method || value is DatatypeCtor);
        //modifies parent;
        parent = value;
      }
    }
    public TypeParameter(IToken tok, string name)
      : base(tok, name, null) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);

    }
  }

  public class ModuleDecl : Declaration {
    public readonly List<string/*!*/>/*!*/ Imports;
    public readonly List<TopLevelDecl/*!*/> TopLevelDecls = new List<TopLevelDecl/*!*/>();  // filled in by the parser; readonly after that
    public readonly Graph<MemberDecl/*!*/> CallGraph = new Graph<MemberDecl/*!*/>();  // filled in during resolution
    public int Height;  // height in the topological sorting of modules; filled in during resolution

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Imports));
      Contract.Invariant(cce.NonNullElements(TopLevelDecls));
      Contract.Invariant(CallGraph != null);
    }


    public ModuleDecl(IToken tok, string name, [Captured] List<string/*!*/>/*!*/ imports, Attributes attributes)
      : base(tok, name, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(imports));
      Imports = imports;

    }
    public virtual bool IsDefaultModule {
      get {
        return false;
      }
    }
  }

  public class DefaultModuleDecl : ModuleDecl {
    public DefaultModuleDecl() : base(Token.NoToken, "_default", new List<string/*!*/>(), null) {
    }
    public override bool IsDefaultModule {
      get {
        return true;
      }
    }
  }

  public abstract class TopLevelDecl : Declaration, TypeParameter.ParentType {
    public readonly ModuleDecl Module;
    public readonly List<TypeParameter/*!*/>/*!*/ TypeArgs;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Module != null);
      Contract.Invariant(cce.NonNullElements(TypeArgs));
    }


    public TopLevelDecl(IToken/*!*/ tok, string/*!*/ name, ModuleDecl/*!*/ module, List<TypeParameter/*!*/>/*!*/ typeArgs, Attributes attributes)
      : base(tok, name, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Module = module;
      TypeArgs = typeArgs;
    }
  }

  public class ClassDecl : TopLevelDecl {
    public readonly List<MemberDecl/*!*/>/*!*/ Members;
    public bool HasConstructor;  // filled in (early) during resolution; true iff there exists a member that is a Constructor
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Members));
    }

    public ClassDecl(IToken/*!*/ tok, string/*!*/ name, ModuleDecl/*!*/ module,
      List<TypeParameter/*!*/>/*!*/ typeArgs, [Captured] List<MemberDecl/*!*/>/*!*/ members, Attributes attributes)
      : base(tok, name, module, typeArgs, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(members));


      Members = members;
    }
    public virtual bool IsDefaultClass {
      get {
        return false;
      }
    }
  }

  public class ClassRefinementDecl : ClassDecl {
    public readonly IToken/*!*/ RefinedClass;
    public ClassDecl Refined; // filled in during resolution 
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(RefinedClass != null);
    }

    public ClassRefinementDecl(IToken tok, string name, ModuleDecl module, List<TypeParameter/*!*/>/*!*/ typeArgs,
      [Captured] List<MemberDecl/*!*/>/*!*/ members, Attributes attributes, IToken/*!*/ refinedClass)
      : base(tok, name, module, typeArgs, members, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(members));
      Contract.Requires(refinedClass != null);
      RefinedClass = refinedClass;
    }
  }

  public class DefaultClassDecl : ClassDecl {
    public DefaultClassDecl(DefaultModuleDecl/*!*/ module, [Captured] List<MemberDecl/*!*/>/*!*/ members)
      : base(Token.NoToken, "_default", module, new List<TypeParameter/*!*/>(), members, null) {
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(members));
    }
    public override bool IsDefaultClass {
      get {
        return true;
      }
    }
  }

  public class ArrayClassDecl : ClassDecl {
    public readonly int Dims;
    public ArrayClassDecl(int dims, ModuleDecl module)
    : base(Token.NoToken, BuiltIns.ArrayClassName(dims), module,
      new List<TypeParameter>(new TypeParameter[]{new TypeParameter(Token.NoToken, "arg")}),
      new List<MemberDecl>(), null)
    {
      Contract.Requires(1 <= dims);
      Contract.Requires(module != null);

      Dims = dims;
    }
  }
  
  public class DatatypeDecl : TopLevelDecl {
    public readonly List<DatatypeCtor/*!*/>/*!*/ Ctors;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Ctors));
      Contract.Invariant(1 <= Ctors.Count);
    }

    public DatatypeCtor DefaultCtor;  // set during resolution

    public DatatypeDecl(IToken/*!*/ tok, string/*!*/ name, ModuleDecl/*!*/ module, List<TypeParameter/*!*/>/*!*/ typeArgs,
      [Captured] List<DatatypeCtor/*!*/>/*!*/ ctors, Attributes attributes)
      : base(tok, name, module, typeArgs, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ctors));
      Contract.Invariant(1 <= ctors.Count);
      Ctors = ctors;
    }
  }

  public class DatatypeCtor : Declaration, TypeParameter.ParentType {
    public readonly List<Formal/*!*/>/*!*/ Formals;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Formals));
      Contract.Invariant(Destructors != null);
      Contract.Invariant(
        Destructors.Count == 0 || // this is until resolution
        Destructors.Count == Formals.Count);  // after resolution
    }

    // TODO: One could imagine having a precondition on datatype constructors
    public DatatypeDecl EnclosingDatatype;  // filled in during resolution
    public SpecialField QueryField;  // filled in during resolution
    public List<SpecialField/*may be null*/> Destructors = new List<SpecialField/*may be null*/>();  // contents filled in during resolution

    public DatatypeCtor(IToken/*!*/ tok, string/*!*/ name, [Captured] List<Formal/*!*/>/*!*/ formals, Attributes attributes)
      : base(tok, name, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(formals));
      this.Formals = formals;
    }

    public string FullName {
      get {
        Contract.Requires(EnclosingDatatype != null);
        Contract.Ensures(Contract.Result<string>() != null);

        return "#" + EnclosingDatatype.Name + "." + Name;
      }
    }
  }

  public abstract class MemberDecl : Declaration {
    public readonly bool IsStatic;
    public TopLevelDecl EnclosingClass;  // filled in during resolution

    public MemberDecl(IToken tok, string name, bool isStatic, Attributes attributes)
      : base(tok, name, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      IsStatic = isStatic;
    }
    /// <summary>
    /// Returns className+"."+memberName.  Available only after resolution.
    /// </summary>
    public string FullName {
      get {
        Contract.Requires(EnclosingClass != null);
        Contract.Ensures(Contract.Result<string>() != null);

        return EnclosingClass.Name + "." + Name;
      }
    }
  }

  public class Field : MemberDecl {
    public readonly bool IsGhost;
    public readonly bool IsMutable;
    public readonly Type Type;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Type != null);
    }

    public Field(IToken tok, string name, bool isGhost, Type type, Attributes attributes)
      : this(tok, name, isGhost, true, type, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
    }

    public Field(IToken tok, string name, bool isGhost, bool isMutable, Type type, Attributes attributes)
      : base(tok, name, false, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      IsGhost = isGhost;
      IsMutable = isMutable;
      Type = type;
    }
  }

  public class SpecialField : Field
  {
    public readonly string CompiledName;
    public readonly string PreString;
    public readonly string PostString;
    public SpecialField(IToken tok, string name, string compiledName, string preString, string postString, bool isGhost, bool isMutable, Type type, Attributes attributes)
      : base(tok, name, isGhost, isMutable, type, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(compiledName != null);
      Contract.Requires(preString != null);
      Contract.Requires(postString != null);
      Contract.Requires(type != null);

      CompiledName = compiledName;
      PreString = preString;
      PostString = postString;
    }
  }

  public class CouplingInvariant : MemberDecl {
    public readonly Expression Expr;
    public readonly List<IToken/*!*/>/*!*/ Toks;
    public List<Formal/*!*/> Formals; // filled in during resolution
    public List<Field/*!*/> Refined; // filled in during resolution

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Expr != null);
      Contract.Invariant(cce.NonNullElements(Toks));
      Contract.Invariant(cce.NonNullElements(Formals));
      Contract.Invariant(cce.NonNullElements(Refined));
    }


    public CouplingInvariant(List<IToken/*!*/>/*!*/ toks, Expression/*!*/ expr, Attributes attributes)
      : base(toks[0], "_coupling_invariant" + getNames(toks), false, attributes) {
      Contract.Requires(toks.Count > 0);
      Expr = expr;
      Toks = toks;
    }

    private static string getNames(List<IToken> toks) {
      Contract.Requires(toks != null);
      Contract.Ensures(Contract.Result<string>() != null);

      StringBuilder sb = new StringBuilder();
      foreach (IToken tok in toks) {
        Contract.Assert(tok != null);
        sb.Append("_").Append(tok.val);
      }
      return sb.ToString();
    }

    public string[] Tokens() {
      string[] result = new string[Toks.Count];
      for (int i = 0; i < Toks.Count; i++)
        result[i] = Toks[i].val;
      return result;
    }
  }

  [ContractClass(typeof(IVariableContracts))]
  public interface IVariable {
    string/*!*/ Name {
      get;
    }
    string/*!*/ UniqueName {
      get;
    }
    Type/*!*/ Type {
      get;
    }
    bool IsMutable {
      get;
    }
    bool IsGhost {
      get;
    }
  }
  [ContractClassFor(typeof(IVariable))]
  public abstract class IVariableContracts : IVariable {
    public string Name {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();
      }
    }
    public string UniqueName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();
      }
    }
    public Type Type {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);
        throw new NotImplementedException();
      }
    }
    public bool IsMutable {
      get {
        throw new NotImplementedException();
      }
    }
    public bool IsGhost {
      get {
        throw new NotImplementedException();
      }
    }
  }

  public abstract class NonglobalVariable : IVariable {
    public readonly IToken tok;
    readonly string name;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
      Contract.Invariant(name != null);
      Contract.Invariant(type != null);
    }

    public string Name {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return name;
      }
    }
    readonly int varId = varIdCount++;
    public string UniqueName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return name + "#" + varId;
      }
    }
    Type type;
    //[Pure(false)]  // TODO: if Type gets the status of [Frozen], then this attribute is not needed
    public Type/*!*/ Type {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);
        return type.Normalize();
      }
    }
    public abstract bool IsMutable {
      get;
    }
    bool isGhost;  // readonly, except for BoundVar's of match expressions/statements during resolution
    public bool IsGhost {
      get {
        return isGhost;
      }
      set {
        isGhost = value;
      }
    }

    public NonglobalVariable(IToken tok, string name, Type type, bool isGhost) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      this.tok = tok;
      this.name = name;
      this.type = type;
      this.isGhost = isGhost;
    }

    internal static int varIdCount;  // this varIdCount is used for both NonglobalVariable's and VarDecl's.
  }

  public class Formal : NonglobalVariable {
    public readonly bool InParam;  // true to in-parameter, false for out-parameter
    public override bool IsMutable {
      get {
        return !InParam;
      }
    }

    public Formal(IToken/*!*/ tok, string/*!*/ name, Type/*!*/ type, bool inParam, bool isGhost)
      : base(tok, name, type, isGhost) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      InParam = inParam;
    }

    public bool HasName {
      get {
        return !Name.StartsWith("#");
      }
    }
  }

  public class BoundVar : NonglobalVariable {
    public override bool IsMutable {
      get {
        return false;
      }
    }

    public BoundVar(IToken/*!*/ tok, string/*!*/ name, Type/*!*/ type)
      : base(tok, name, type, false) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
    }
  }

  public class Function : MemberDecl, TypeParameter.ParentType {
    public readonly bool IsGhost;  // functions are "ghost" by default; a non-ghost function is called a "function method"
    public readonly bool IsUnlimited;
    public bool IsRecursive;  // filled in during resolution
    public readonly List<TypeParameter/*!*/>/*!*/ TypeArgs;
    public readonly List<Formal/*!*/>/*!*/ Formals;
    public readonly Type/*!*/ ResultType;
    public readonly List<Expression/*!*/>/*!*/ Req;
    public readonly List<FrameExpression/*!*/>/*!*/ Reads;
    public readonly List<Expression/*!*/>/*!*/ Ens;
    public readonly List<Expression/*!*/>/*!*/ Decreases;
    public readonly Expression Body;  // an extended expression
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(TypeArgs));
      Contract.Invariant(cce.NonNullElements(Formals));
      Contract.Invariant(ResultType != null);
      Contract.Invariant(cce.NonNullElements(Req));
      Contract.Invariant(cce.NonNullElements(Reads));
      Contract.Invariant(cce.NonNullElements(Ens));
      Contract.Invariant(cce.NonNullElements(Decreases));
    }


    public Function(IToken tok, string name, bool isStatic, bool isGhost, bool isUnlimited, [Captured] List<TypeParameter/*!*/>/*!*/ typeArgs,
                    [Captured] List<Formal/*!*/>/*!*/ formals, Type/*!*/ resultType, List<Expression/*!*/>/*!*/ req, List<FrameExpression/*!*/>/*!*/ reads,
                    List<Expression/*!*/>/*!*/ ens, List<Expression/*!*/>/*!*/ decreases, Expression body, Attributes attributes)
      : base(tok, name, isStatic, attributes) {

      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(formals));
      Contract.Requires(resultType != null);
      Contract.Requires(cce.NonNullElements(req));
      Contract.Requires(cce.NonNullElements(reads));
      Contract.Requires(cce.NonNullElements(ens));
      Contract.Requires(cce.NonNullElements(decreases));
      this.IsGhost = isGhost;
      this.IsUnlimited = isUnlimited;
      this.TypeArgs = typeArgs;
      this.Formals = formals;
      this.ResultType = resultType;
      this.Req = req;
      this.Reads = reads;
      this.Ens = ens;
      this.Decreases = decreases;
      this.Body = body;
    }
  }

  public class Method : MemberDecl, TypeParameter.ParentType {
    public readonly bool IsGhost;
    public readonly List<TypeParameter/*!*/>/*!*/ TypeArgs;
    public readonly List<Formal/*!*/>/*!*/ Ins;
    public readonly List<Formal/*!*/>/*!*/ Outs;
    public readonly List<MaybeFreeExpression/*!*/>/*!*/ Req;
    public readonly List<FrameExpression/*!*/>/*!*/ Mod;
    public readonly List<MaybeFreeExpression/*!*/>/*!*/ Ens;
    public readonly List<Expression/*!*/>/*!*/ Decreases;
    public readonly BlockStmt Body;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(TypeArgs));
      Contract.Invariant(cce.NonNullElements(Ins));
      Contract.Invariant(cce.NonNullElements(Outs));
      Contract.Invariant(cce.NonNullElements(Req));
      Contract.Invariant(cce.NonNullElements(Mod));
      Contract.Invariant(cce.NonNullElements(Ens));
      Contract.Invariant(cce.NonNullElements(Decreases));
    }

    public Method(IToken tok, string name,
                  bool isStatic, bool isGhost,
                  [Captured] List<TypeParameter/*!*/>/*!*/ typeArgs,
                  [Captured] List<Formal/*!*/>/*!*/ ins, [Captured] List<Formal/*!*/>/*!*/ outs,
                  [Captured] List<MaybeFreeExpression/*!*/>/*!*/ req, [Captured] List<FrameExpression/*!*/>/*!*/ mod,
                  [Captured] List<MaybeFreeExpression/*!*/>/*!*/ ens,
                  [Captured] List<Expression/*!*/>/*!*/ decreases,
                  [Captured] BlockStmt body,
                  Attributes attributes)
      : base(tok, name, isStatic, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ins));
      Contract.Requires(cce.NonNullElements(outs));
      Contract.Requires(cce.NonNullElements(req));
      Contract.Requires(cce.NonNullElements(mod));
      Contract.Requires(cce.NonNullElements(ens));
      Contract.Requires(cce.NonNullElements(decreases));
      this.IsGhost = isGhost;
      this.TypeArgs = typeArgs;
      this.Ins = ins;
      this.Outs = outs;
      this.Req = req;
      this.Mod = mod;
      this.Ens = ens;
      this.Decreases = decreases;
      this.Body = body;
    }
  }

  public class Constructor : Method
  {
    public Constructor(IToken tok, string name,
                  [Captured] List<TypeParameter/*!*/>/*!*/ typeArgs,
                  [Captured] List<Formal/*!*/>/*!*/ ins,
                  [Captured] List<MaybeFreeExpression/*!*/>/*!*/ req, [Captured] List<FrameExpression/*!*/>/*!*/ mod,
                  [Captured] List<MaybeFreeExpression/*!*/>/*!*/ ens,
                  [Captured] List<Expression/*!*/>/*!*/ decreases,
                  [Captured] BlockStmt body,
                  Attributes attributes)
      : base(tok, name, false, false, typeArgs, ins, new List<Formal>(), req, mod, ens, decreases, body, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ins));
      Contract.Requires(cce.NonNullElements(req));
      Contract.Requires(cce.NonNullElements(mod));
      Contract.Requires(cce.NonNullElements(ens));
      Contract.Requires(cce.NonNullElements(decreases));
    }
  }

  public class MethodRefinement : Method
  {
    public Method Refined; // filled in during resolution
    public MethodRefinement(IToken/*!*/ tok, string/*!*/ name,
                  bool isStatic, bool isGhost,
                  [Captured] List<TypeParameter/*!*/>/*!*/ typeArgs,
                  [Captured] List<Formal/*!*/>/*!*/ ins, [Captured] List<Formal/*!*/>/*!*/ outs,
                  [Captured] List<MaybeFreeExpression/*!*/>/*!*/ req, [Captured] List<FrameExpression/*!*/>/*!*/ mod,
                  [Captured] List<MaybeFreeExpression/*!*/>/*!*/ ens,
                  [Captured] List<Expression/*!*/>/*!*/ decreases,
                  [Captured] BlockStmt body,
                  Attributes attributes)
      : base(tok, name, isStatic, isGhost, typeArgs, ins, outs, req, mod, ens, decreases, body, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ins));
      Contract.Requires(cce.NonNullElements(outs));
      Contract.Requires(cce.NonNullElements(req));
      Contract.Requires(cce.NonNullElements(mod));
      Contract.Requires(cce.NonNullElements(ens));
      Contract.Requires(cce.NonNullElements(decreases));
    }
  }

  // ------------------------------------------------------------------------------------------------------

  public abstract class Statement {
    public readonly IToken Tok;
    public LabelNode Labels;  // mutable during resolution

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Tok != null);
    }

    public bool IsGhost;  // filled in by resolution
    public Statement(IToken tok) {
      Contract.Requires(tok != null);
      this.Tok = tok;
    }
  }

  public class LabelNode
  {
    public readonly IToken Tok;
    public readonly string Label;
    public readonly int UniqueId;
    public readonly LabelNode Next;
    static int nodes = 0;

    public LabelNode(IToken tok, string label, LabelNode next) {
      Contract.Requires(tok != null);
      Tok = tok;
      Label = label;
      Next = next;
      UniqueId = nodes++;
    }
  }

  public abstract class PredicateStmt : Statement
  {
    [Peer]
    public readonly Expression Expr;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Expr != null);
    }

    [Captured]
    public PredicateStmt(IToken tok, Expression expr)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      Contract.Ensures(cce.Owner.Same(this, expr));
      cce.Owner.AssignSame(this, expr);
      this.Expr = expr;
    }
  }

  public class AssertStmt : PredicateStmt {
    [Captured]
    public AssertStmt(IToken/*!*/ tok, Expression/*!*/ expr)
      : base(tok, expr) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      Contract.Ensures(cce.Owner.Same(this, expr));

    }
  }

  public class AssumeStmt : PredicateStmt {
    [Captured]
    public AssumeStmt(IToken/*!*/ tok, Expression/*!*/ expr)
      : base(tok, expr) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      Contract.Ensures(cce.Owner.Same(this, expr));

    }
  }

  public class PrintStmt : Statement {
    public readonly List<Attributes.Argument/*!*/>/*!*/ Args;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Args));
    }

    public PrintStmt(IToken tok, List<Attributes.Argument/*!*/>/*!*/ args)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(args));

      Args = args;
    }
  }

  public class BreakStmt : Statement {
    public readonly string TargetLabel;
    public readonly int BreakCount;
    public Statement TargetStmt;  // filled in during resolution
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(TargetLabel == null || 1 <= BreakCount);
    }

    public BreakStmt(IToken tok, string targetLabel)
      : base(tok) {
      Contract.Requires(tok != null);
      this.TargetLabel = targetLabel;
    }
    public BreakStmt(IToken tok, int breakCount)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(1 <= breakCount);
      this.BreakCount = breakCount;
    }
  }

  public class ReturnStmt : Statement {
    public List<AssignmentRhs> rhss;
    public UpdateStmt hiddenUpdate;
    public ReturnStmt(IToken tok, List<AssignmentRhs> rhss)
      : base(tok) {
      Contract.Requires(tok != null);
      this.rhss = rhss;
      hiddenUpdate = null;
    }
  }

  public abstract class AssignmentRhs {
    public readonly IToken Tok;
    internal AssignmentRhs(IToken tok) {
      Tok = tok;
    }
    public abstract bool CanAffectPreviouslyKnownExpressions { get; }
  }

  public class ExprRhs : AssignmentRhs
  {
    public readonly Expression Expr;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Expr != null);
    }

    public ExprRhs(Expression expr)
      : base(expr.tok)
    {
      Contract.Requires(expr != null);
      Expr = expr;
    }
    public override bool CanAffectPreviouslyKnownExpressions { get { return false; } }
  }

  public class TypeRhs : AssignmentRhs
  {
    public readonly Type EType;
    public readonly List<Expression> ArrayDimensions;
    public CallStmt InitCall;  // may be null (and is definitely null for arrays)
    public Type Type;  // filled in during resolution
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(EType != null);
      Contract.Invariant(ArrayDimensions == null || 1 <= ArrayDimensions.Count);
      Contract.Invariant(ArrayDimensions == null || InitCall == null);
    }

    public TypeRhs(IToken tok, Type type)
      : base(tok)
    {
      Contract.Requires(type != null);
      EType = type;
    }
    public TypeRhs(IToken tok, Type type, CallStmt initCall)
      : base(tok)
    {
      Contract.Requires(type != null);
      EType = type;
      InitCall = initCall;
    }
    public TypeRhs(IToken tok, Type type, List<Expression> arrayDimensions)
      : base(tok)
    {
      Contract.Requires(type != null);
      Contract.Requires(arrayDimensions != null && 1 <= arrayDimensions.Count);
      EType = type;
      ArrayDimensions = arrayDimensions;
    }
    public override bool CanAffectPreviouslyKnownExpressions {
      get {
        if (InitCall != null) {
          foreach (var mod in InitCall.Method.Mod) {
            if (!(mod.E is ThisExpr)) {
              return true;
            }
          }
        }
        return false;
      }
    }
  }

  public class CallRhs : AssignmentRhs
  {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Receiver != null);
      Contract.Invariant(MethodName != null);
      Contract.Invariant(cce.NonNullElements(Args));
    }

    public readonly Expression/*!*/ Receiver;
    public readonly string/*!*/ MethodName;
    public readonly List<Expression/*!*/>/*!*/ Args;
    public Method Method;  // filled in by resolution

    public CallRhs(IToken tok, Expression/*!*/ receiver, string/*!*/ methodName, List<Expression/*!*/>/*!*/ args)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(receiver != null);
      Contract.Requires(methodName != null);
      Contract.Requires(cce.NonNullElements(args));

      this.Receiver = receiver;
      this.MethodName = methodName;
      this.Args = args;
    }
    // TODO: Investigate this. For an initialization, this is true. But for existing objects, this is not true.
    public override bool CanAffectPreviouslyKnownExpressions {
      get {
        foreach (var mod in Method.Mod) {
          if (!(mod.E is ThisExpr)) {
            return true;
          }
        }
        return false;
      }
    }
  }

  public class HavocRhs : AssignmentRhs {
    public HavocRhs(IToken tok)
      : base(tok)
    {
    }
    public override bool CanAffectPreviouslyKnownExpressions { get { return false; } }
  }

  public abstract class ConcreteSyntaxStatement : Statement
  {
    public List<Statement> ResolvedStatements = new List<Statement>();  // contents filled in during resolution
    public ConcreteSyntaxStatement(IToken tok)
      : base(tok) {
    }
  }

  public class VarDeclStmt : ConcreteSyntaxStatement
  {
    public readonly List<VarDecl> Lhss;
    public readonly UpdateStmt Update;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Lhss));
    }

    public VarDeclStmt(IToken tok, List<VarDecl> lhss, UpdateStmt update)
      : base(tok)
    {
      Contract.Requires(lhss != null);

      Lhss = lhss;
      Update = update;
    }
  }

  public class UpdateStmt : ConcreteSyntaxStatement
  {
    public readonly List<Expression> Lhss;
    public readonly List<AssignmentRhs> Rhss;
    public readonly bool CanMutateKnownState;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Lhss));
      Contract.Invariant(cce.NonNullElements(Rhss));
    }
    public UpdateStmt(IToken tok, List<Expression> lhss, List<AssignmentRhs> rhss)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(lhss));
      Contract.Requires(cce.NonNullElements(rhss));
      Contract.Requires(lhss.Count != 0 || rhss.Count == 1);
      Lhss = lhss;
      Rhss = rhss;
      CanMutateKnownState = false;
    }
    public UpdateStmt(IToken tok, List<Expression> lhss, List<AssignmentRhs> rhss, bool mutate)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(lhss));
      Contract.Requires(cce.NonNullElements(rhss));
      Contract.Requires(lhss.Count != 0 || rhss.Count == 1);
      Lhss = lhss;
      Rhss = rhss;
      CanMutateKnownState = mutate;
    }
  }

  public class AssignStmt : Statement {
    public readonly Expression/*!*/ Lhs;
    public readonly AssignmentRhs/*!*/ Rhs;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Lhs != null);
      Contract.Invariant(Rhs != null);
    }

    public AssignStmt(IToken tok, Expression lhs, AssignmentRhs rhs)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(lhs != null);
      Contract.Requires(rhs != null);
      this.Lhs = lhs;
      this.Rhs = rhs;
    }
  }

  public class VarDecl : Statement, IVariable {
    readonly string/*!*/ name;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(name != null);
      Contract.Invariant(OptionalType != null);
    }

    public VarDecl(IToken tok, string name, Type type, bool isGhost)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);  // can be a proxy, though

      this.name = name;
      this.OptionalType = type;
      this.IsGhost = isGhost;
    }

    public string/*!*/ Name {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return name;
      }
    }
    readonly int varId = NonglobalVariable.varIdCount++;
    public string/*!*/ UniqueName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return name + "#" + varId;
      }
    }
    public readonly Type OptionalType;  // this is the type mentioned in the declaration, if any
    internal Type type;  // this is the declared or inferred type of the variable; it is non-null after resolution (even if resolution fails)
    //[Pure(false)]
    public Type Type {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);

        Contract.Assume(type != null);  /* we assume object has been resolved */
        return type.Normalize();
      }
    }
    public bool IsMutable {
      get {
        return true;
      }
    }
    bool IVariable.IsGhost {
      get {
        return base.IsGhost;
      }
    }
    /// <summary>
    /// This method retrospectively makes the VarDecl a ghost.  It is to be used only during resolution.
    /// </summary>
    public void MakeGhost() {
      base.IsGhost = true;
    }
  }

  public class CallStmt : Statement {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      //Contract.Invariant(Receiver != null);
      Contract.Invariant(MethodName != null);
      Contract.Invariant(cce.NonNullElements(Lhs));
      Contract.Invariant(cce.NonNullElements(Args));
    }

    public readonly List<Expression/*!*/>/*!*/ Lhs;
    public Expression/*!*/ Receiver;
    public readonly string/*!*/ MethodName;
    public readonly List<Expression/*!*/>/*!*/ Args;
    public Method Method;  // filled in by resolution

    public CallStmt(IToken tok, List<Expression/*!*/>/*!*/ lhs, Expression/*!*/ receiver,
      string/*!*/ methodName, List<Expression/*!*/>/*!*/ args)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(lhs));
      Contract.Requires(methodName != null);
      Contract.Requires(cce.NonNullElements(args));

      this.Lhs = lhs;
      this.Receiver = receiver;
      this.MethodName = methodName;
      this.Args = args;
    }
  }

  public class BlockStmt : Statement {
    public readonly List<Statement/*!*/>/*!*/ Body;
    public BlockStmt(IToken/*!*/ tok, [Captured] List<Statement/*!*/>/*!*/ body)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(body));
      this.Body = body;

    }
  }

  public class IfStmt : Statement {
    public readonly Expression Guard;
    public readonly Statement Thn;
    public readonly Statement Els;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Thn != null);
      Contract.Invariant(Els == null || Els is BlockStmt || Els is IfStmt);
    }
    public IfStmt(IToken tok, Expression guard, Statement thn, Statement els)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(guard != null);
      Contract.Requires(thn != null);
      Contract.Requires(els == null || els is BlockStmt || els is IfStmt);
      this.Guard = guard;
      this.Thn = thn;
      this.Els = els;

    }
  }

  public class GuardedAlternative
  {
    public readonly IToken Tok;
    public readonly Expression Guard;
    public readonly List<Statement> Body;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Tok != null);
      Contract.Invariant(Guard != null);
      Contract.Invariant(Body != null);
    }
    public GuardedAlternative(IToken tok, Expression guard, List<Statement> body)
    {
      Contract.Requires(tok != null);
      Contract.Requires(guard != null);
      Contract.Requires(body != null);
      this.Tok = tok;
      this.Guard = guard;
      this.Body = body;
    }
  }

  public class AlternativeStmt : Statement
  {
    public readonly List<GuardedAlternative> Alternatives;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Alternatives != null);
    }
    public AlternativeStmt(IToken tok, List<GuardedAlternative> alternatives)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(alternatives != null);
      this.Alternatives = alternatives;
    }
  }

  public abstract class LoopStmt : Statement
  {
    public readonly List<MaybeFreeExpression/*!*/>/*!*/ Invariants;
    public readonly List<Expression/*!*/>/*!*/ Decreases;
    public readonly List<FrameExpression/*!*/>/*!*/ Mod;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Invariants));
      Contract.Invariant(cce.NonNullElements(Decreases));
      Contract.Invariant(Mod == null || cce.NonNullElements(Mod));
    }
    public LoopStmt(IToken tok, List<MaybeFreeExpression/*!*/>/*!*/ invariants, List<Expression/*!*/>/*!*/ decreases, List<FrameExpression/*!*/>/*!*/ mod)
    : base(tok) 
    {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(invariants));
      Contract.Requires(cce.NonNullElements(decreases));
      Contract.Requires(mod == null || cce.NonNullElements(mod));

      this.Invariants = invariants;
      this.Decreases = decreases;
      this.Mod = mod;
    }
  }

  public class WhileStmt : LoopStmt
  {
    public readonly Expression Guard;
    public readonly Statement/*!*/ Body;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Body != null);
    }

    public WhileStmt(IToken tok, Expression guard,
                     List<MaybeFreeExpression/*!*/>/*!*/ invariants, List<Expression/*!*/>/*!*/ decreases, List<FrameExpression/*!*/> mod,
                     Statement/*!*/ body)
      : base(tok, invariants, decreases, mod) {
      Contract.Requires(tok != null);
      Contract.Requires(body != null);
      this.Guard = guard;
      this.Body = body;
    }
  }

  public class AlternativeLoopStmt : LoopStmt
  {
    public readonly List<GuardedAlternative> Alternatives;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Alternatives != null);
    }
    public AlternativeLoopStmt(IToken tok,
                               List<MaybeFreeExpression/*!*/>/*!*/ invariants, List<Expression/*!*/>/*!*/ decreases, List<FrameExpression/*!*/> mod,
                               List<GuardedAlternative> alternatives)
      : base(tok, invariants, decreases, mod) {
      Contract.Requires(tok != null);
      Contract.Requires(alternatives != null);
      this.Alternatives = alternatives;
    }
  }

  public class ForeachStmt : Statement
  {
    public readonly BoundVar/*!*/ BoundVar;
    public readonly Expression/*!*/ Collection;
    public readonly Expression/*!*/ Range;
    public readonly List<PredicateStmt/*!*/>/*!*/ BodyPrefix;
    public readonly Statement GivenBody;  // used only until resolution; afterwards, use BodyAssign
    public AssignStmt/*!*/ BodyAssign;  // filled in during resolution
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(BoundVar != null);
      Contract.Invariant(Collection != null);
      Contract.Invariant(Range != null);
      Contract.Invariant(cce.NonNullElements(BodyPrefix));
      Contract.Invariant(GivenBody != null);
    }

    public ForeachStmt(IToken tok, BoundVar boundVar, Expression collection, Expression range,
      List<PredicateStmt/*!*/>/*!*/ bodyPrefix, Statement givenBody)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(boundVar != null);
      Contract.Requires(collection != null);
      Contract.Requires(range != null);
      Contract.Requires(cce.NonNullElements(bodyPrefix));
      Contract.Requires(givenBody != null);
      this.BoundVar = boundVar;
      this.Collection = collection;
      this.Range = range;
      this.BodyPrefix = bodyPrefix;
      this.GivenBody = givenBody;
    }
  }

  public class MatchStmt : Statement {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Source != null);
      Contract.Invariant(cce.NonNullElements(Cases));
      Contract.Invariant(cce.NonNullElements(MissingCases));
    }

    public readonly Expression Source;
    public readonly List<MatchCaseStmt/*!*/>/*!*/ Cases;
    public readonly List<DatatypeCtor/*!*/> MissingCases = new List<DatatypeCtor>();  // filled in during resolution

    public MatchStmt(IToken tok, Expression source, [Captured] List<MatchCaseStmt/*!*/>/*!*/ cases)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(source != null);
      Contract.Requires(cce.NonNullElements(cases));
      this.Source = source;
      this.Cases = cases;

    }
  }

  public class MatchCaseStmt : MatchCase
  {
    public readonly List<Statement/*!*/>/*!*/ Body;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Body));
    }

    public MatchCaseStmt(IToken tok, string id, [Captured] List<BoundVar/*!*/>/*!*/ arguments, [Captured] List<Statement/*!*/>/*!*/ body)
      : base(tok, id, arguments)
    {
      Contract.Requires(tok != null);
      Contract.Requires(id != null);
      Contract.Requires(cce.NonNullElements(arguments));
      Contract.Requires(cce.NonNullElements(body));
      this.Body = body;
    }
  }

  // ------------------------------------------------------------------------------------------------------

  public class NestedToken : IToken
  {
    public NestedToken(IToken outer, IToken inner) {
      Outer = outer;
      Inner = inner;
    }
    public readonly IToken Outer;
    public readonly IToken Inner;

    public int col {
      get { return Outer.col; }
      set { Outer.col = value; }
    }
    public string filename {
      get { return Outer.filename; }
      set { Outer.filename = value; }
    }
    public bool IsValid {
      get { return Outer.IsValid; }
    }
    public int kind {
      get { return Outer.kind; }
      set { Outer.kind = value; }
    }
    public int line {
      get { return Outer.line; }
      set { Outer.line = value; }
    }
    public int pos {
      get { return Outer.pos; }
      set { Outer.pos = value; }
    }
    public string val {
      get { return Outer.val; }
      set { Outer.val = value; }
    }
  }

  // ------------------------------------------------------------------------------------------------------

  public abstract class Expression
  {
    public readonly IToken tok;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
    }

    public Expression Resolved {
      get {
        Contract.Requires(type != null);  // should be called only on resolved expressions; this approximates that precondition
        Expression r = this;
        while (true) {
          var rr = r as ConcreteSyntaxExpression;
          if (rr == null) { break; }
          r = rr.ResolvedExpression;
        }
        return r;
      }
    }

    protected Type type;
    public Type Type {  // filled in during resolution
      [Verify(false)]  // TODO: how do we allow Type.get to modify type and still be [Pure]?
      [Additive]  // validity of proper subclasses is not required
      get {
        Contract.Ensures(type != null || Contract.Result<Type>() == null);  // useful in conjunction with postcondition of constructor
        return type == null ? null : type.Normalize();
      }
      [NoDefaultContract]  // no particular validity of 'this' is required, except that it not be committed
      set {
        Contract.Requires(cce.IsValid(this));
        Contract.Requires(Type == null);  // set it only once
        Contract.Requires(value != null);
        //modifies type;
        type = value.Normalize();
      }
    }

    public Expression(IToken tok) {
      Contract.Requires(tok != null);
      Contract.Ensures(type == null);  // we would have liked to have written Type==null, but that's not admissible or provable

      this.tok = tok;
    }

    /// <summary>
    /// Returns the non-null subexpressions of the Expression.
    /// </summary>
    public virtual IEnumerable<Expression> SubExpressions {
      get { yield break; }
    }
  }

  /// <summary>
  /// Instances of this class are introduced during resolution to indicate that a static method or function has
  /// been invoked without specifying a receiver (that is, by just giving the name of the enclosing class).
  /// </summary>
  public class StaticReceiverExpr : LiteralExpr
  {
    public StaticReceiverExpr(IToken tok, ClassDecl cl)
      : base(tok)  // constructs a LiteralExpr representing the 'null' literal
    {
      Contract.Requires(tok != null);
      Contract.Requires(cl != null);
      var typeArgs = new List<Type>();
      foreach (var ta in cl.TypeArgs) {
        typeArgs.Add(new InferredTypeProxy());
      }
      Type = new UserDefinedType(tok, cl.Name, cl, typeArgs);
    }
  }

  public class LiteralExpr : Expression {
    public readonly object Value;

    public static bool IsTrue(Expression e) {
      Contract.Requires(e != null);
      if (e is LiteralExpr) {
        LiteralExpr le = (LiteralExpr)e;
        return le.Value is bool && (bool)le.Value;
      } else {
        return false;
      }
    }

    public LiteralExpr(IToken tok)
      : base(tok) {  // represents the Dafny literal "null"
      Contract.Requires(tok != null);
      this.Value = null;

    }

    public LiteralExpr(IToken tok, BigInteger n)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(0 <= n.Sign);

      this.Value = n;

    }

    public LiteralExpr(IToken tok, int n) :base(tok){
      Contract.Requires(tok != null);
      Contract.Requires(0 <= n);

      this.Value = new BigInteger(n);
    }

    public LiteralExpr(IToken tok, bool b)
      : base(tok) {
      Contract.Requires(tok != null);
      this.Value = b;

    }
  }

  public class DatatypeValue : Expression {
    public readonly string DatatypeName;
    public readonly string MemberName;
    public readonly List<Expression/*!*/>/*!*/ Arguments;
    public DatatypeCtor Ctor;  // filled in by resolution
    public List<Type/*!*/> InferredTypeArgs = new List<Type>();  // filled in by resolution
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(DatatypeName != null);
      Contract.Invariant(MemberName != null);
      Contract.Invariant(cce.NonNullElements(Arguments));
      Contract.Invariant(cce.NonNullElements(InferredTypeArgs));
    }

    public DatatypeValue(IToken tok, string datatypeName, string memberName, [Captured] List<Expression/*!*/>/*!*/ arguments)
      : base(tok) {
      Contract.Requires(cce.NonNullElements(arguments));
      Contract.Requires(tok != null);
      Contract.Requires(datatypeName != null);
      Contract.Requires(memberName != null);
      this.DatatypeName = datatypeName;
      this.MemberName = memberName;
      this.Arguments = arguments;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { return Arguments; }
    }
  }

  public class ThisExpr : Expression {
    public ThisExpr(IToken tok)
      : base(tok) {
      Contract.Requires(tok != null);
    }
  }

  public class ImplicitThisExpr : ThisExpr {
    public ImplicitThisExpr(IToken tok)
      : base(tok) {
      Contract.Requires(tok != null);
    }
  }

  public class IdentifierExpr : Expression
  {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Name != null);
    }

    public readonly string Name;
    public IVariable Var;  // filled in by resolution

    public IdentifierExpr(IToken tok, string name)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Name = name;
    }
  }

  /// <summary>
  /// If an "AutoGhostIdentifierExpr" is used as the out-parameter of a ghost method or
  /// a method with a ghost parameter, resolution will change the .Var's .IsGhost to true
  /// automatically.  This class is intended to be used only as a communicate between the
  /// parser and parts of the resolver.
  /// </summary>
  public class AutoGhostIdentifierExpr : IdentifierExpr
  {
    public AutoGhostIdentifierExpr(IToken tok, string name)
      : base(tok, name) { }
  }

  public abstract class DisplayExpression : Expression {
    public readonly List<Expression/*!*/>/*!*/ Elements;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Elements));
    }

    public DisplayExpression(IToken tok, List<Expression/*!*/>/*!*/ elements)
      : base(tok) {
      Contract.Requires(cce.NonNullElements(elements));
      Elements = elements;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { return Elements; }
    }
  }

  public class SetDisplayExpr : DisplayExpression {
    public SetDisplayExpr(IToken tok, List<Expression/*!*/>/*!*/ elements)
      : base(tok, elements) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(elements));
    }
  }

  public class SeqDisplayExpr : DisplayExpression {
    public SeqDisplayExpr(IToken tok, List<Expression/*!*/>/*!*/ elements)
      : base(tok, elements) {
      Contract.Requires(cce.NonNullElements(elements));
      Contract.Requires(tok != null);
    }
  }

  public class FieldSelectExpr : Expression {
    public readonly Expression Obj;
    public readonly string FieldName;
    public Field Field;  // filled in by resolution

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Obj != null);
      Contract.Invariant(FieldName != null);
    }

    public FieldSelectExpr(IToken tok, Expression obj, string fieldName)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(obj != null);
      Contract.Requires(fieldName != null);
      this.Obj = obj;
      this.FieldName = fieldName;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return Obj; }
    }
  }

  public class SeqSelectExpr : Expression {
    public readonly bool SelectOne;  // false means select a range
    public readonly Expression Seq;
    public readonly Expression E0;
    public readonly Expression E1;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Seq != null);
      Contract.Invariant(!SelectOne || E1 == null);
      Contract.Invariant(E0 != null || E1 != null);
    }

    public SeqSelectExpr(IToken tok, bool selectOne, Expression seq, Expression e0, Expression e1)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(seq != null);
      Contract.Requires(!selectOne || e1 == null);
      Contract.Requires(e0 != null || e1 != null);

      SelectOne = selectOne;
      Seq = seq;
      E0 = e0;
      E1 = e1;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Seq;
        if (E0 != null) yield return E0;
        if (E1 != null) yield return E1;
      }
    }
  }

  public class MultiSelectExpr : Expression {
    public readonly Expression Array;
    public readonly List<Expression> Indices;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Array != null);
      Contract.Invariant(cce.NonNullElements(Indices));
      Contract.Invariant(1 <= Indices.Count);
    }

    public MultiSelectExpr(IToken tok, Expression array, List<Expression> indices)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(array != null);
      Contract.Requires(cce.NonNullElements(indices) && 1 <= indices.Count);

      Array = array;
      Indices = indices;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Array;
        foreach (var e in Indices) {
          yield return e;
        }
      }
    }
  }

  public class SeqUpdateExpr : Expression {
    public readonly Expression Seq;
    public readonly Expression Index;
    public readonly Expression Value;

    public SeqUpdateExpr(IToken tok, Expression seq, Expression index, Expression val)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(seq != null);
      Contract.Requires(index != null);
      Contract.Requires(val != null);
      Seq = seq;
      Index = index;
      Value = val;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Seq;
        yield return Index;
        yield return Value;
      }
    }
  }

  public class FunctionCallExpr : Expression {
    public readonly string/*!*/ Name;
    [Peer]
    public readonly Expression/*!*/ Receiver;
    [Peer]
    public readonly List<Expression/*!*/>/*!*/ Args;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Name != null);
      Contract.Invariant(Receiver != null);
      Contract.Invariant(cce.NonNullElements(Args));
    }

    public Function Function;  // filled in by resolution

    [Captured]
    public FunctionCallExpr(IToken tok, string fn, Expression receiver, [Captured] List<Expression/*!*/>/*!*/ args)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(fn != null);
      Contract.Requires(receiver != null);
      Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(type == null);
      Contract.Ensures(cce.Owner.Same(this, receiver));


      this.Name = fn;
      cce.Owner.AssignSame(this, receiver);
      this.Receiver = receiver;
      this.Args = args;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Receiver;
        foreach (var e in Args) {
          yield return e;
        }
      }
    }
  }

  public class OldExpr : Expression {
    [Peer]
    public readonly Expression E;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
    }

    [Captured]
    public OldExpr(IToken tok, Expression expr)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      cce.Owner.AssignSame(this, expr);
      E = expr;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return E; }
    }
  }

  public class FreshExpr : Expression {
    public readonly Expression E;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
    }

    public FreshExpr(IToken tok, Expression expr)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      E = expr;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return E; }
    }
  }

  public class AllocatedExpr : Expression
  {
    public readonly Expression E;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
    }

    public AllocatedExpr(IToken tok, Expression expr)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      E = expr;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return E; }
    }
  }

  public class UnaryExpr : Expression
  {
    public enum Opcode {
      Not,
      SetChoose,  // Important: SetChoose is not a function, so it can only be used in a statement context (in particular, the RHS of an assignment)
      SeqLength
    }
    public readonly Opcode Op;
    public readonly Expression E;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
    }

    public UnaryExpr(IToken tok, Opcode op, Expression e)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
      this.Op = op;
      this.E = e;

    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return E; }
    }
  }

  public class BinaryExpr : Expression {
    public enum Opcode {
      Iff,
      Imp,
      And,
      Or,
      Eq,
      Neq,
      Lt,
      Le,
      Ge,
      Gt,
      Disjoint,
      In,
      NotIn,
      Add,
      Sub,
      Mul,
      Div,
      Mod
    }
    public readonly Opcode Op;
    public enum ResolvedOpcode {
      // logical operators
      Iff,
      Imp,
      And,
      Or,
      // non-collection types
      EqCommon,
      NeqCommon,
      // integers
      Lt,
      Le,
      Ge,
      Gt,
      Add,
      Sub,
      Mul,
      Div,
      Mod,
      // sets
      SetEq,
      SetNeq,
      ProperSubset,
      Subset,
      Superset,
      ProperSuperset,
      Disjoint,
      InSet,
      NotInSet,
      Union,
      Intersection,
      SetDifference,
      // sequences
      SeqEq,
      SeqNeq,
      ProperPrefix,
      Prefix,
      Concat,
      InSeq,
      NotInSeq,
      // datatypes
      RankLt,
      RankGt
    }
    public ResolvedOpcode ResolvedOp;  // filled in by resolution

    public static string OpcodeString(Opcode op) {
      Contract.Ensures(Contract.Result<string>() != null);

      switch (op) {
        case Opcode.Iff:
          return "<==>";
        case Opcode.Imp:
          return "==>";
        case Opcode.And:
          return "&&";
        case Opcode.Or:
          return "||";
        case Opcode.Eq:
          return "==";
        case Opcode.Lt:
          return "<";
        case Opcode.Gt:
          return ">";
        case Opcode.Le:
          return "<=";
        case Opcode.Ge:
          return ">=";
        case Opcode.Neq:
          return "!=";
        case Opcode.Disjoint:
          return "!!";
        case Opcode.In:
          return "in";
        case Opcode.NotIn:
          return "!in";
        case Opcode.Add:
          return "+";
        case Opcode.Sub:
          return "-";
        case Opcode.Mul:
          return "*";
        case Opcode.Div:
          return "/";
        case Opcode.Mod:
          return "%";
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException();  // unexpected operator
      }
    }
    public readonly Expression E0;
    public readonly Expression E1;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E0 != null);
      Contract.Invariant(E1 != null);
    }


    public BinaryExpr(IToken tok, Opcode op, Expression e0, Expression e1)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      this.Op = op;
      this.E0 = e0;
      this.E1 = e1;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return E0;
        yield return E1;
      }
    }
  }

  /// <summary>
  /// A ComprehensionExpr has the form:
  ///   BINDER x Attributes | Range(x) :: Term(x)
  /// When BINDER is "forall" or "exists", the range may be "null" (which stands for the logical value "true").
  /// For other BINDERs (currently, "set"), the range is non-null.
  /// where "Attributes" is optional, and "| Range(x)" is optional and defaults to "true".
  /// Currently, BINDER is one of the logical quantifiers "exists" or "forall".
  /// </summary>
  public abstract class ComprehensionExpr : Expression {
    public readonly List<BoundVar/*!*/>/*!*/ BoundVars;
    public readonly Expression Range;
    public readonly Expression/*!*/ Term;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(BoundVars != null);
      Contract.Invariant(Term != null);
    }

    public readonly Attributes Attributes;

    public abstract class BoundedPool { }
    public class IntBoundedPool : BoundedPool
    {
      public readonly Expression LowerBound;
      public readonly Expression UpperBound;
      public IntBoundedPool(Expression lowerBound, Expression upperBound) {
        LowerBound = lowerBound;
        UpperBound = upperBound;
      }
    }
    public class SetBoundedPool : BoundedPool
    {
      public readonly Expression Set;
      public SetBoundedPool(Expression set) { Set = set; }
    }
    public class SeqBoundedPool : BoundedPool
    {
      public readonly Expression Seq;
      public SeqBoundedPool(Expression seq) { Seq = seq; }
    }
    public class BoolBoundedPool : BoundedPool
    {
    }

    public List<BoundedPool> Bounds;  // initialized and filled in by resolver
    // invariant Bounds == null || Bounds.Count == BoundVars.Count;
    public List<BoundVar> MissingBounds;  // filled in during resolution; remains "null" if bounds can be found 
    // invariant Bounds == null || MissingBounds == null;

    public ComprehensionExpr(IToken/*!*/ tok, List<BoundVar/*!*/>/*!*/ bvars, Expression range, Expression/*!*/ term, Attributes attrs)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(term != null);

      this.BoundVars = bvars;
      this.Range = range;
      this.Term = term;
      this.Attributes = attrs;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        if (Range != null) { yield return Range; }
        yield return Term; 
      }
    }
  }

  public abstract class QuantifierExpr : ComprehensionExpr {
    public readonly Triggers Trigs;

    public QuantifierExpr(IToken/*!*/ tok, List<BoundVar/*!*/>/*!*/ bvars, Expression range, Expression/*!*/ term, Triggers trigs, Attributes attrs)
      : base(tok, bvars, range, term, attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(term != null);

      this.Trigs = trigs;
    }
    public abstract Expression/*!*/ LogicalBody();
  }

  public class Triggers {
    public readonly List<Expression/*!*/>/*!*/ Terms;
    public readonly Triggers Prev;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Terms));
    }

    public Triggers(List<Expression/*!*/>/*!*/ terms, Triggers prev) {
      Contract.Requires(cce.NonNullElements(terms));
      this.Terms = terms;
      this.Prev = prev;
    }
  }

  public class ForallExpr : QuantifierExpr {
    public ForallExpr(IToken tok, List<BoundVar/*!*/>/*!*/ bvars, Expression range, Expression term, Triggers trig, Attributes attrs)
      : base(tok, bvars, range, term, trig, attrs) {
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(tok != null);
      Contract.Requires(term != null);
    }
    public override Expression/*!*/ LogicalBody() {
      if (Range == null) {
        return Term;
      }
      var body = new BinaryExpr(Term.tok, BinaryExpr.Opcode.Imp, Range, Term);
      body.ResolvedOp = BinaryExpr.ResolvedOpcode.Imp;
      body.Type = Term.Type;
      return body;
    }
  }

  public class ExistsExpr : QuantifierExpr {
    public ExistsExpr(IToken tok, List<BoundVar/*!*/>/*!*/ bvars, Expression range, Expression term, Triggers trig, Attributes attrs)
      : base(tok, bvars, range, term, trig, attrs) {
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(tok != null);
      Contract.Requires(term != null);
    }
    public override Expression/*!*/ LogicalBody() {
      if (Range == null) {
        return Term;
      }
      var body = new BinaryExpr(Term.tok, BinaryExpr.Opcode.And, Range, Term);
      body.ResolvedOp = BinaryExpr.ResolvedOpcode.And;
      body.Type = Term.Type;
      return body;
    }
  }

  public class SetComprehension : ComprehensionExpr
  {
    public readonly bool TermIsImplicit;

    public SetComprehension(IToken/*!*/ tok, List<BoundVar/*!*/>/*!*/ bvars, Expression/*!*/ range, Expression term)
      : base(tok, bvars, range, term ?? new IdentifierExpr(tok, bvars[0].Name), null) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(1 <= bvars.Count);
      Contract.Requires(range != null);

      TermIsImplicit = term == null;
    }
  }

  public class WildcardExpr : Expression
  {  // a WildcardExpr can occur only in reads clauses and a loop's decreases clauses (with different meanings)
    public WildcardExpr(IToken tok)
      : base(tok) {
      Contract.Requires(tok != null);
    }
  }

  public class ITEExpr : Expression {
    public readonly Expression Test;
    public readonly Expression Thn;
    public readonly Expression Els;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Test != null);
      Contract.Invariant(Thn != null);
      Contract.Invariant(Els != null);
    }

    public ITEExpr(IToken tok, Expression test, Expression thn, Expression els)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(test != null);
      Contract.Requires(thn != null);
      Contract.Requires(els != null);
      this.Test = test;
      this.Thn = thn;
      this.Els = els;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Test;
        yield return Thn;
        yield return Els;
      }
    }
  }

  public class MatchExpr : Expression {  // a MatchExpr is an "extended expression" and is only allowed in certain places
    public readonly Expression Source;
    public readonly List<MatchCaseExpr/*!*/>/*!*/ Cases;
    public readonly List<DatatypeCtor/*!*/> MissingCases = new List<DatatypeCtor>();  // filled in during resolution

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Source != null);
      Contract.Invariant(cce.NonNullElements(Cases));
      Contract.Invariant(cce.NonNullElements(MissingCases));
    }

    public MatchExpr(IToken tok, Expression source, [Captured] List<MatchCaseExpr/*!*/>/*!*/ cases)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(source != null);
      Contract.Requires(cce.NonNullElements(cases));
      this.Source = source;
      this.Cases = cases;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Source;
        foreach (var mc in Cases) {
          yield return mc.Body;
        }
      }
    }
  }

  public abstract class MatchCase
  {
    public readonly IToken tok;
    public readonly string Id;
    public DatatypeCtor Ctor;  // filled in by resolution
    public readonly List<BoundVar/*!*/>/*!*/ Arguments;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
      Contract.Invariant(Id != null);
      Contract.Invariant(cce.NonNullElements(Arguments));
    }

    public MatchCase(IToken tok, string id, [Captured] List<BoundVar/*!*/>/*!*/ arguments) {
      Contract.Requires(tok != null);
      Contract.Requires(id != null);
      Contract.Requires(cce.NonNullElements(arguments));
      this.tok = tok;
      this.Id = id;
      this.Arguments = arguments;
    }
  }

  public class MatchCaseExpr : MatchCase
  {
    public readonly Expression/*!*/ Body;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Body != null);
    }

    public MatchCaseExpr(IToken tok, string id, [Captured] List<BoundVar/*!*/>/*!*/ arguments, Expression body)
      : base(tok, id, arguments)
    {
      Contract.Requires(tok != null);
      Contract.Requires(id != null);
      Contract.Requires(cce.NonNullElements(arguments));
      Contract.Requires(body != null);
      this.Body = body;
    }
  }

  public class BoxingCastExpr : Expression {  // a BoxingCastExpr is used only as a temporary placeholding during translation
    public readonly Expression E;
    public readonly Type FromType;
    public readonly Type ToType;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
      Contract.Invariant(FromType != null);
      Contract.Invariant(ToType != null);
    }

    public BoxingCastExpr(Expression e, Type fromType, Type toType)
      : base(e.tok) {
      Contract.Requires(e != null);
      Contract.Requires(fromType != null);
      Contract.Requires(toType != null);

      E = e;
      FromType = fromType;
      ToType = toType;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return E; }
    }
  }

  public class UnboxingCastExpr : Expression {  // an UnboxingCastExpr is used only as a temporary placeholding during translation
    public readonly Expression E;
    public readonly Type FromType;
    public readonly Type ToType;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
      Contract.Invariant(FromType != null);
      Contract.Invariant(ToType != null);
    }

    public UnboxingCastExpr(Expression e, Type fromType, Type toType)
      : base(e.tok) {
      Contract.Requires(e != null);
      Contract.Requires(fromType != null);
      Contract.Requires(toType != null);

      E = e;
      FromType = fromType;
      ToType = toType;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return E; }
    }
  }

  public class MaybeFreeExpression {
    public readonly Expression E;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
    }

    public readonly bool IsFree;
    public MaybeFreeExpression(Expression e, bool isFree) {
      Contract.Requires(e != null);
      E = e;
      IsFree = isFree;
    }
  }

  public class FrameExpression {
    public readonly Expression E;  // may be a WildcardExpr
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
      Contract.Invariant(!(E is WildcardExpr) || FieldName == null && Field == null);
    }

    public readonly string FieldName;
    public Field Field;  // filled in during resolution (but is null if FieldName is)

    public FrameExpression(Expression e, string fieldName) {
      Contract.Requires(e != null);
      Contract.Requires(!(e is WildcardExpr) || fieldName == null);

      E = e;
      FieldName = fieldName;
    }
  }

  /// <summary>
  /// This class represents a piece of concrete syntax in the parse tree.  During resolution,
  /// it gets "replaced" by the expression in "ResolvedExpression".
  /// </summary>
  public abstract class ConcreteSyntaxExpression : Expression
  {
    public Expression ResolvedExpression;  // filled in during resolution; after resolution, manipulation of "this" should proceed as with manipulating "this.ResolvedExpression"
    public ConcreteSyntaxExpression(IToken tok)
      : base(tok) {
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        if (ResolvedExpression != null) {
          yield return ResolvedExpression;
        }
      }
    }
  }

  public class ParensExpression : ConcreteSyntaxExpression
  {
    public readonly Expression E;
    public ParensExpression(IToken tok, Expression e)
      : base(tok) {
      E = e;
    }
  }

  public class ChainingExpression : ConcreteSyntaxExpression
  {
    public readonly List<Expression> Operands;
    public readonly List<BinaryExpr.Opcode> Operators;
    public readonly Expression E;
    public ChainingExpression(IToken tok, List<Expression> operands, List<BinaryExpr.Opcode> operators, Expression desugaring)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(operands != null);
      Contract.Requires(operators != null);
      Contract.Requires(desugaring != null);
      Contract.Requires(operators.Count == operators.Count + 1);

      Operands = operands;
      Operators = operators;
      E = desugaring;
    }
  }

  public class IdentifierSequence : ConcreteSyntaxExpression
  {
    public readonly List<IToken> Tokens;
    public readonly IToken OpenParen;
    public readonly List<Expression> Arguments;
    public IdentifierSequence(List<IToken> tokens, IToken openParen, List<Expression> args)
      : base(tokens[0]) {
      Contract.Requires(tokens != null && 1 <= tokens.Count);
      /* "args" is null to indicate the absence of a parenthesized suffix */
      Contract.Requires(args == null || openParen != null);

      Tokens = tokens;
      OpenParen = openParen;
      Arguments = args;
    }
  }
}
