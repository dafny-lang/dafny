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
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class Program {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(FullName != null);
      Contract.Invariant(DefaultModule != null);
    }

    public readonly string FullName;
    public List<ModuleDefinition> Modules; // filled in during resolution.
                                                     // Resolution essentially flattens the module hierarchy, for
                                                     // purposes of translation and compilation.
    public List<ModuleDefinition> CompileModules; // filled in during resolution.
                                                  // Contains the definitions to be used for compilation.

    List<AdditionalInformation> _additionalInformation = new List<AdditionalInformation>();
    public List<AdditionalInformation> AdditionalInformation { get { return _additionalInformation; } }
    public readonly ModuleDecl DefaultModule;
    public readonly ModuleDefinition DefaultModuleDef;
    public readonly BuiltIns BuiltIns;
    public readonly List<TranslationTask> TranslationTasks;
    public Program(string name, [Captured] ModuleDecl module, [Captured] BuiltIns builtIns) {
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(module is LiteralModuleDecl);
      FullName = name;
      DefaultModule = module;
      DefaultModuleDef = (DefaultModuleDecl)((LiteralModuleDecl)module).ModuleDef;
      BuiltIns = builtIns;
      Modules = new List<ModuleDefinition>();
      CompileModules = new List<ModuleDefinition>();
      TranslationTasks = new List<TranslationTask>();
    }

    public string Name
    {
      get
      {
        try
        {
          return System.IO.Path.GetFileName(FullName);
        }
        catch (ArgumentException)
        {
          return FullName;
        }
      }
    }
  }

  public class Include : IComparable
  {
    public readonly IToken tok;
    public readonly string filename;
    public readonly string fullPath;

    public Include(IToken tok, string theFilename, string fullPath) {
      this.tok = tok;
      this.filename = theFilename;
      this.fullPath = fullPath;
    }


    public int CompareTo(object obj) {
      var i = obj as Include;
      if (i != null) {
        return this.fullPath.CompareTo(i.fullPath);
      } else {
        throw new NotImplementedException();
      }
    }
  }

  public class BuiltIns
  {
    public readonly ModuleDefinition SystemModule = new ModuleDefinition(Token.NoToken, "_System", false, false, null, null, null, true);
    readonly Dictionary<int, ClassDecl> arrayTypeDecls = new Dictionary<int, ClassDecl>();
    readonly Dictionary<int, ArrowTypeDecl> arrowTypeDecls = new Dictionary<int, ArrowTypeDecl>();
    readonly Dictionary<int, TupleTypeDecl> tupleTypeDecls = new Dictionary<int, TupleTypeDecl>();

    public readonly ClassDecl ObjectDecl;
    public BuiltIns() {
      SystemModule.Height = -1;  // the system module doesn't get a height assigned later, so we set it here to something below everything else
      // create type synonym 'string'
      var str = new TypeSynonymDecl(Token.NoToken, "string", new List<TypeParameter>(), SystemModule, new SeqType(new CharType()), null);
      SystemModule.TopLevelDecls.Add(str);
      // create class 'object'
      ObjectDecl = new ClassDecl(Token.NoToken, "object", SystemModule, new List<TypeParameter>(), new List<MemberDecl>(), DontCompile(), null);
      SystemModule.TopLevelDecls.Add(ObjectDecl);
      // add one-dimensional arrays, since they may arise during type checking
      // Arrays of other dimensions may be added during parsing as the parser detects the need for these
      UserDefinedType tmp = ArrayType(1, Type.Int, true);
      // Arrow types of other dimensions may be added during parsing as the parser detects the need for these.  For the 0-arity
      // arrow type, the resolver adds a Valid() predicate for iterators, whose corresponding arrow type is conveniently created here.
      CreateArrowTypeDecl(0);
      // Note, in addition to these types, the _System module contains tuple types.  These tuple types are added to SystemModule
      // by the parser as the parser detects the need for these.
    }

    private Attributes DontCompile() {
      var flse = Expression.CreateBoolLiteral(Token.NoToken, false);
      return new Attributes("compile", new List<Expression>() { flse }, null);
    }

    public UserDefinedType ArrayType(int dims, Type arg, bool allowCreationOfNewClass) {
      Contract.Requires(1 <= dims);
      Contract.Requires(arg != null);
      return ArrayType(Token.NoToken, dims, new List<Type>() { arg }, allowCreationOfNewClass);
    }
    public UserDefinedType ArrayType(IToken tok, int dims, List<Type> typeArgs, bool allowCreationOfNewClass) {
      Contract.Requires(tok != null);
      Contract.Requires(1 <= dims);
      Contract.Requires(typeArgs != null);
      Contract.Ensures(Contract.Result<UserDefinedType>() != null);

      UserDefinedType udt = new UserDefinedType(tok, ArrayClassName(dims), typeArgs, null);
      if (allowCreationOfNewClass && !arrayTypeDecls.ContainsKey(dims)) {
        ArrayClassDecl arrayClass = new ArrayClassDecl(dims, SystemModule, DontCompile());
        for (int d = 0; d < dims; d++) {
          string name = dims == 1 ? "Length" : "Length" + d;
          string compiledName = dims == 1 ? "Length" : "GetLength(" + d + ")";
          Field len = new SpecialField(Token.NoToken, name, compiledName, "new BigInteger(", ")", false, false, false, Type.Int, null);
          len.EnclosingClass = arrayClass;  // resolve here
          arrayClass.Members.Add(len);
        }
        arrayTypeDecls.Add(dims, arrayClass);
        SystemModule.TopLevelDecls.Add(arrayClass);
      }
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

    /// <summary>
    /// Idempotently add an arrow type with arity 'arity' to the system module.
    /// </summary>
    public void CreateArrowTypeDecl(int arity) {
      Contract.Requires(0 <= arity);
      if (!arrowTypeDecls.ContainsKey(arity)) {
        IToken tok = Token.NoToken;
        var tps = Util.Map(Enumerable.Range(0, arity + 1),
          x => new TypeParameter(tok, "T" + x));
        var tys = tps.ConvertAll(tp => (Type)(new UserDefinedType(tp)));
        var args = Util.Map(Enumerable.Range(0, arity), i => new Formal(tok, "x" + i, tys[i], true, false));
        var argExprs = args.ConvertAll(a =>
              (Expression)new IdentifierExpr(tok, a.Name) { Var = a, Type = a.Type });
        var readsIS = new FunctionCallExpr(tok, "reads", new ImplicitThisExpr(tok), tok, argExprs) {
          Type = new SetType(new ObjectType()),
        };
        var readsFrame = new List<FrameExpression> { new FrameExpression(tok, readsIS, null) };
        var req = new Function(tok, "requires", false, true,
          new List<TypeParameter>(), args, Type.Bool,
          new List<Expression>(), readsFrame, new List<Expression>(),
          new Specification<Expression>(new List<Expression>(), null),
          null, null, null);
        var reads = new Function(tok, "reads", false, true,
          new List<TypeParameter>(), args, new SetType(new ObjectType()),
          new List<Expression>(), readsFrame, new List<Expression>(),
          new Specification<Expression>(new List<Expression>(), null),
          null, null, null);
        readsIS.Function = reads;  // just so we can really claim the member declarations are resolved
        readsIS.TypeArgumentSubstitutions = Util.Dict(tps, tys);  // ditto
        var arrowDecl = new ArrowTypeDecl(tps, req, reads, SystemModule, DontCompile());
        arrowTypeDecls.Add(arity, arrowDecl);
        SystemModule.TopLevelDecls.Add(arrowDecl);
      }
    }

    public TupleTypeDecl TupleType(IToken tok, int dims, bool allowCreationOfNewType) {
      Contract.Requires(tok != null);
      Contract.Requires(0 <= dims);
      Contract.Ensures(Contract.Result<TupleTypeDecl>() != null);

      TupleTypeDecl tt;
      if (!tupleTypeDecls.TryGetValue(dims, out tt)) {
        Contract.Assume(allowCreationOfNewType);  // the parser should ensure that all needed tuple types exist by the time of resolution
        tt = new TupleTypeDecl(dims, SystemModule);
        tupleTypeDecls.Add(dims, tt);
        SystemModule.TopLevelDecls.Add(tt);
      }
      return tt;
    }
    public static string TupleTypeName(int dims) {
      Contract.Requires(0 <= dims);
      return "_tuple#" + dims;
    }
    public static bool IsTupleTypeName(string s) {
      Contract.Requires(s != null);
      return s.StartsWith("_tuple#");
    }
    public const string TupleTypeCtorName = "_#Make";  // the printer wants this name to be uniquely recognizable
  }

  public class Attributes {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Name != null);
      Contract.Invariant(cce.NonNullElements(Args));
    }

    public string Name;
    /*Frozen*/
    public readonly List<Expression> Args;
    public readonly Attributes Prev;

    public Attributes(string name, [Captured] List<Expression> args, Attributes prev) {
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(args));
      Name = name;
      Args = args;
      Prev = prev;
    }

    public static IEnumerable<Expression> SubExpressions(Attributes attrs) {
      for (; attrs != null; attrs = attrs.Prev) {
        foreach (var arg in attrs.Args) {
          yield return arg;
        }
      }
    }

    public static bool Contains(Attributes attrs, string nm) {
      Contract.Requires(nm != null);
      for (; attrs != null; attrs = attrs.Prev) {
        if (attrs.Name == nm) {
          return true;
        }
      }
      return false;
    }

    /// <summary>
    /// Returns true if "nm" is a specified attribute.  If it is, then:
    /// - if the attribute is {:nm true}, then value==true
    /// - if the attribute is {:nm false}, then value==false
    /// - if the attribute is anything else, then value returns as whatever it was passed in as.
    /// </summary>
    [Pure]
    public static bool ContainsBool(Attributes attrs, string nm, ref bool value) {
      Contract.Requires(nm != null);
      for (; attrs != null; attrs = attrs.Prev) {
        if (attrs.Name == nm) {
          if (attrs.Args.Count == 1) {
            var arg = attrs.Args[0] as LiteralExpr;
            if (arg != null && arg.Value is bool) {
              value = (bool)arg.Value;
            }
          }
          return true;
        }
      }
      return false;
    }

    /// <summary>
    /// Checks whether a Boolean attribute has been set on the declaration itself,
    /// the enclosing class, or any enclosing module.  Settings closer to the declaration
    /// override those further away.
    /// </summary>
    public static bool ContainsBoolAtAnyLevel(MemberDecl decl, string attribName) {
      bool setting = true;
      if (Attributes.ContainsBool(decl.Attributes, attribName, ref setting)) {
        return setting;
      }

      if (Attributes.ContainsBool(decl.EnclosingClass.Attributes, attribName, ref setting)) {
        return setting;
      }

      // Check the entire stack of modules
      var mod = decl.EnclosingClass.Module;
      while (mod != null) {
        if (Attributes.ContainsBool(mod.Attributes, attribName, ref setting)) {
          return setting;
        }
        mod = mod.Module;
      }

      return false;
    }
  }

  // ------------------------------------------------------------------------------------------------------

  public abstract class Type {
    public static readonly BoolType Bool = new BoolType();
    public static readonly CharType Char = new CharType();
    public static readonly IntType Int = new IntType();
    public static readonly RealType Real = new RealType();

    // Type arguments to the type
    public List<Type> TypeArgs = new List<Type> { };

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

    [Pure]
    public abstract string TypeName(ModuleDefinition/*?*/ context);
    [Pure]
    public override string ToString() {
      return TypeName(null);
    }

    /// <summary>
    /// Return the most constrained version of "this", getting to the bottom of proxies.
    /// </summary>
    public Type Normalize() {
      Contract.Ensures(Contract.Result<Type>() != null);
      Type type = this;
      while (true) {
        var pt = type as TypeProxy;
        if (pt != null && pt.T != null) {
          type = pt.T;
        } else {
          return type;
        }
      }
    }

    /// <summary>
    /// Return the type that "this" stands for, getting to the bottom of proxies and following type synonyms.
    /// </summary>
    [Pure]
    public Type NormalizeExpand() {
      Contract.Ensures(Contract.Result<Type>() != null);
      Contract.Ensures(!(Contract.Result<Type>() is TypeProxy) || ((TypeProxy)Contract.Result<Type>()).T == null);  // return a proxy only if .T == null
      Type type = this;
      while (true) {
        var pt = type as TypeProxy;
        if (pt != null && pt.T != null) {
          type = pt.T;
        } else {
          var syn = type.AsTypeSynonym;
          if (syn != null) {
            var udt = (UserDefinedType)type;  // correctness of cast follows from the AsTypeSynonym != null test.
            // Instantiate with the actual type arguments
            type = syn.RhsWithArgument(udt.TypeArgs);
          } else {
            return type;
          }
        }
      }
    }

    /// <summary>
    /// Returns whether or not "this" and "that" denote the same type, module proxies and type synonyms.
    /// </summary>
    [Pure]
    public abstract bool Equals(Type that);

    public bool IsBoolType { get { return NormalizeExpand() is BoolType; } }
    public bool IsCharType { get { return NormalizeExpand() is CharType; } }
    public bool IsIntegerType { get { return NormalizeExpand() is IntType; } }
    public bool IsRealType { get { return NormalizeExpand() is RealType; } }
    public bool IsSubrangeType {
      get { return NormalizeExpand() is NatType; }
    }
    public bool IsNumericBased() {
      var t = NormalizeExpand();
      var opProxy = t as OperationTypeProxy;
      if (opProxy != null) {
        return (opProxy.AllowInts || opProxy.AllowReals) && !opProxy.AllowChar && !opProxy.AllowSeq && !opProxy.AllowSetVarieties;
      }
      return t.IsIntegerType || t.IsRealType || t.AsNewtype != null;
    }
    public enum NumericPersuation { Int, Real }
    [Pure]
    public bool IsNumericBased(NumericPersuation p) {
      Type t = this;
      while (true) {
        t = t.NormalizeExpand();
        if (t.IsIntegerType) {
          return p == NumericPersuation.Int;
        } else if (t.IsRealType) {
          return p == NumericPersuation.Real;
        }
        var proxy = t as OperationTypeProxy;
        if (proxy != null) {
          if (proxy.JustInts) {
            return p == NumericPersuation.Int;
          } else if (proxy.JustReals) {
            return p == NumericPersuation.Real;
          }
        }
        var d = t.AsNewtype;
        if (d == null) {
          return false;
        }
        t = d.BaseType;
      }
    }

    public CollectionType AsCollectionType { get { return NormalizeExpand() as CollectionType; } }
    public SetType AsSetType { get { return NormalizeExpand() as SetType; } }
    public MultiSetType AsMultiSetType { get { return NormalizeExpand() as MultiSetType; } }
    public SeqType AsSeqType { get { return NormalizeExpand() as SeqType; } }
    public MapType AsMapType { get { return NormalizeExpand() as MapType; } }

    public bool IsRefType {
      get {
        var t = NormalizeExpand();
        if (t is ObjectType) {
          return true;
        } else {
          var udt = t as UserDefinedType;
          return udt != null && udt.ResolvedParam == null && udt.ResolvedClass is ClassDecl
            && !(udt.ResolvedClass is ArrowTypeDecl);
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
        var t = NormalizeExpand();
        var udt = UserDefinedType.DenotesClass(t);
        return udt == null ? null : udt.ResolvedClass as ArrayClassDecl;
      }
    }
    public bool IsArrowType {
      get { return AsArrowType != null; }
    }
    public ArrowType AsArrowType {
      get {
        var t = NormalizeExpand();
        return t as ArrowType;
      }
    }
    public NewtypeDecl AsNewtype {
      get {
        var udt = NormalizeExpand() as UserDefinedType;
        return udt == null ? null : udt.ResolvedClass as NewtypeDecl;
      }
    }
    public TypeSynonymDecl AsTypeSynonym {
      get {
        var udt = this as UserDefinedType;  // note, it is important to use 'this' here, not 'this.NormalizeExpand()'
        if (udt == null) {
          return null;
        } else {
          return udt.ResolvedClass as TypeSynonymDecl;
        }
      }
    }
    public RedirectingTypeDecl AsRedirectingType {
      get {
        var udt = this as UserDefinedType;  // Note, it is important to use 'this' here, not 'this.NormalizeExpand()'.  This property getter is intended to be used during resolution.
        if (udt == null) {
          return null;
        } else {
          return (RedirectingTypeDecl)(udt.ResolvedClass as TypeSynonymDecl) ?? udt.ResolvedClass as NewtypeDecl;
        }
      }
    }
    public bool IsDatatype {
      get {
        return AsDatatype != null;
      }
    }
    public DatatypeDecl AsDatatype {
      get {
        var udt = NormalizeExpand() as UserDefinedType;
        if (udt == null) {
          return null;
        } else {
          return udt.ResolvedClass as DatatypeDecl;
        }
      }
    }
    public bool IsIndDatatype {
      get {
        return AsIndDatatype != null;
      }
    }
    public IndDatatypeDecl AsIndDatatype {
      get {
        var udt = NormalizeExpand() as UserDefinedType;
        if (udt == null) {
          return null;
        } else {
          return udt.ResolvedClass as IndDatatypeDecl;
        }
      }
    }
    public bool IsCoDatatype {
      get {
        return AsCoDatatype != null;
      }
    }
    public CoDatatypeDecl AsCoDatatype {
      get {
        var udt = NormalizeExpand() as UserDefinedType;
        if (udt == null) {
          return null;
        } else {
          return udt.ResolvedClass as CoDatatypeDecl;
        }
      }
    }
    public bool InvolvesCoDatatype {
      get {
        return IsCoDatatype;  // TODO: should really check structure of the type recursively
      }
    }
    public bool IsTypeParameter {
      get {
        return AsTypeParameter != null;
      }
    }
    public TypeParameter AsTypeParameter {
      get {
        var ct = NormalizeExpand() as UserDefinedType;
        return ct == null ? null : ct.ResolvedParam;
      }
    }
    public virtual bool SupportsEquality {
      get {
        return true;
      }
    }

    /// <summary>
    /// Returns true if it is known how to meaningfully compare the type's inhabitants.
    /// </summary>
    public bool IsOrdered {
      get {
        return !IsTypeParameter && !IsCoDatatype;
      }
    }

    public void ForeachTypeComponent(Action<Type> action) {
      action(this);
      TypeArgs.ForEach(action);
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
    public override string TypeName(ModuleDefinition context) {
      return "bool";
    }
    public override bool Equals(Type that) {
      return that.IsBoolType;
    }
  }

  public class CharType : BasicType
  {
    [Pure]
    public override string TypeName(ModuleDefinition context) {
      return "char";
    }
    public override bool Equals(Type that) {
      return that.IsCharType;
    }
  }

  public class IntType : BasicType
  {
    [Pure]
    public override string TypeName(ModuleDefinition context) {
      return "int";
    }
    public override bool Equals(Type that) {
      return that.IsIntegerType;
    }
  }

  public class NatType : IntType
  {
    [Pure]
    public override string TypeName(ModuleDefinition context) {
      return "nat";
    }
  }

  public class RealType : BasicType {
    [Pure]
    public override string TypeName(ModuleDefinition context) {
      return "real";
    }
    public override bool Equals(Type that) {
      return that.IsRealType;
    }
  }

  public class ObjectType : BasicType
  {
    [Pure]
    public override string TypeName(ModuleDefinition context) {
      return "object";
    }
    public override bool Equals(Type that) {
      return that.NormalizeExpand() is ObjectType;
    }
  }

  public class ArrowType : UserDefinedType
  {
    public List<Type> Args {
      get { return TypeArgs.GetRange(0, Arity); }
    }

    public Type Result {
      get { return TypeArgs[Arity]; }
    }

    public int Arity {
      get { return TypeArgs.Count - 1; }
    }

    /// <summary>
    /// Constructs a(n unresolved) arrow type.
    /// </summary>
    public ArrowType(IToken tok, List<Type> args, Type result)
      :  base(tok, ArrowTypeName(args.Count), Util.Snoc(args, result), null) {
      Contract.Requires(tok != null);
      Contract.Requires(args != null);
      Contract.Requires(result != null);
    }
    /// <summary>
    /// Constructs and returns a resolved arrow type.
    /// </summary>
    public ArrowType(IToken tok, List<Type> args, Type result, ModuleDefinition systemModule)
      : this(tok, args, result) {
      Contract.Requires(tok != null);
      Contract.Requires(args != null);
      Contract.Requires(result != null);
      Contract.Requires(systemModule != null);
      ResolvedClass = systemModule.TopLevelDecls.Find(d => d.Name == Name);
      Contract.Assume(ResolvedClass != null);
    }

    public const string Arrow_FullCompileName = "Func";  // this is the same for all arities
    public override string FullCompileName {
      get { return Arrow_FullCompileName; }
    }

    public static string ArrowTypeName(int arity) {
      return "_#Func" + arity;
    }

    [Pure]
    public static bool IsArrowTypeName(string s) {
      return s.StartsWith("_#Func");
    }

    public override string TypeName(ModuleDefinition context) {
      var domainNeedsParens = false;
      if (Arity != 1) {
        // 0 or 2-or-more arguments:  need parentheses
        domainNeedsParens = true;
      } else {
        var arg = Args[0].Normalize();  // note, we do Normalize(), not NormalizeExpand(), since the TypeName will use any synonym
        if (arg is ArrowType) {
          // arrows are right associative, so we need parentheses around the domain type
          domainNeedsParens = true;
        } else {
          // if the domain type consists of a single tuple type, then an extra set of parentheses is needed
          // Note, we do NOT call .AsDatatype or .AsIndDatatype here, because those calls will do a NormalizeExpand().  Instead, we do the check manually.
          var udt = arg as UserDefinedType;
          if (udt != null && udt.ResolvedClass is TupleTypeDecl) {
            domainNeedsParens = true;
          }
        }
      }
      string s = "";
      if (domainNeedsParens) { s += "("; }
      s += Util.Comma(Args, arg => arg.TypeName(context));
      if (domainNeedsParens) { s += ")"; }
      s += " -> ";
      s += Result.TypeName(context);
      return s;
    }
   
    public override bool SupportsEquality {
      get {
        return false;
      }
    }
  }

  public abstract class CollectionType : NonProxyType
  {
    public abstract string CollectionTypeName { get; }
    public override string TypeName(ModuleDefinition context) {
      Contract.Ensures(Contract.Result<string>() != null);
      var targs = HasTypeArg() ? "<" + Arg.TypeName(context) + ">" : "";
      return CollectionTypeName + targs;
    }
    public Type Arg {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);  // this is true only after "arg" has really been set (i.e., it follows from the precondition)
        Contract.Assume(arg != null);  // This is really a precondition.  Don't call Arg until "arg" has been set.
        return arg;
      }
    }  // denotes the Domain type for a Map
    private Type arg;
    // The following two methods, HasTypeArg and SetTypeArg, are to be called during resolution to make sure that "arg" becomes set.
    public bool HasTypeArg() {
      return arg != null;
    }
    public void SetTypeArg(Type arg) {
      Contract.Requires(arg != null);
      Contract.Assume(this.arg == null);  // Can only set it once.  This is really a precondition.
      this.arg = arg;
      this.TypeArgs = new List<Type> { arg };
    }
    [ContractInvariantMethod]
    void ObjectInvariant() {
      // Contract.Invariant(Contract.ForAll(TypeArgs, tp => tp != null));
      // After resolution, the following is invariant:  Contract.Invariant(Arg != null);
      // However, it may not be true until then.
    }
    public CollectionType(Type arg) {
      this.arg = arg;
      this.TypeArgs = new List<Type> { arg };
    }
    public override bool SupportsEquality {
      get {
        // Note that all collection types support equality. There is, however, a requirement (checked during resolution)
        // that the argument types of collections support equality.
        return true;
      }
    }
  }

  public class SetType : CollectionType {
    public SetType(Type arg) : base(arg) {
    }
    public override string CollectionTypeName { get { return "set"; } }
    [Pure]
    public override bool Equals(Type that) {
      var t = that.NormalizeExpand() as SetType;
      return t != null && Arg.Equals(t.Arg);
    }
  }

  public class MultiSetType : CollectionType
  {
    public MultiSetType(Type arg) : base(arg) {
    }
    public override string CollectionTypeName { get { return "multiset"; } }
    public override bool Equals(Type that) {
      var t = that.NormalizeExpand() as MultiSetType;
      return t != null && Arg.Equals(t.Arg);
    }
  }

  public class SeqType : CollectionType {
    public SeqType(Type arg) : base(arg) {
    }
    public override string CollectionTypeName { get { return "seq"; } }
    public override bool Equals(Type that) {
      var t = that.NormalizeExpand() as SeqType;
      return t != null && Arg.Equals(t.Arg);
    }
  }
  public class MapType : CollectionType
  {
    public Type Range {
      get { return range; }
      set {
        range = Range;
        TypeArgs = new List<Type> { Arg, range };
      }
    }
    private Type range;
    public void SetRangetype(Type range) {
      Contract.Requires(range != null);
      Contract.Assume(this.range == null);  // Can only set once.  This is really a precondition.
      this.range = range;
    }
    public MapType(Type domain, Type range) : base(domain) {
      Contract.Requires((domain == null && range == null) || (domain != null && range != null));
      this.range = range;
      this.TypeArgs = new List<Type> {domain,range};
    }
    public Type Domain {
      get { return Arg; }
      set {
        TypeArgs = new List<Type> { Domain, range };
      }
    }
    public override string CollectionTypeName { get { return "map"; } }
    [Pure]
    public override string TypeName(ModuleDefinition context) {
      Contract.Ensures(Contract.Result<string>() != null);
      var targs = HasTypeArg() ? "<" + Domain.TypeName(context) + ", " + Range.TypeName(context) + ">" : "";
      return CollectionTypeName + targs;
    }
    public override bool Equals(Type that) {
      var t = that.NormalizeExpand() as MapType;
      return t != null && Arg.Equals(t.Arg) && Range.Equals(t.Range);
    }
  }

  public class UserDefinedType : NonProxyType
  {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
      Contract.Invariant(Name != null);
      Contract.Invariant(cce.NonNullElements(TypeArgs));
      Contract.Invariant(cce.NonNullElements(Path));
      Contract.Invariant(!ArrowType.IsArrowTypeName(Name) || this is ArrowType);
    }

    public readonly List<IToken> Path;
    public readonly IToken tok;  // token of the Name
    public readonly string Name;
    [Rep]

    public string FullName {
      get {
        if (ResolvedClass != null && !ResolvedClass.Module.IsDefaultModule) {
          return ResolvedClass.Module.Name + "." + Name;
        } else {
          return Name;
        }
      }
    }

    string compileName;
    string CompileName {
      get {
        if (compileName == null) {
          compileName = NonglobalVariable.CompilerizeName(Name);
        }
        return compileName;
      }
    }
    public virtual string FullCompileName {
      get {
        if (ResolvedClass != null && !ResolvedClass.Module.IsDefaultModule) {
          return ResolvedClass.Module.CompileName + ".@" + CompileName;
        } else {
          return CompileName;
        }
      }
    }

    public TopLevelDecl ResolvedClass;  // filled in by resolution, if Name denotes a class/datatype/iterator and TypeArgs match the type parameters of that class/datatype/iterator
    public TypeParameter ResolvedParam;  // filled in by resolution, if Name denotes an enclosing type parameter and TypeArgs is the empty list

    public UserDefinedType(IToken tok, string name, [Captured] List<Type> typeArgs, List<IToken> moduleName) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(moduleName == null || cce.NonNullElements(moduleName));
      if (moduleName != null) this.Path = moduleName;
      else this.Path = new List<IToken>();
      this.tok = tok;
      this.Name = name;
      this.TypeArgs = typeArgs;
    }

    /// <summary>
    /// This constructor constructs a resolved class/datatype/iterator type
    /// </summary>
    public UserDefinedType(IToken tok, string name, TopLevelDecl cd, [Captured] List<Type> typeArgs)
      : this(tok, name, cd, typeArgs, null)
    {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cd != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
    }

    /// <summary>
    /// This constructor constructs a resolved class/datatype/iterator type
    /// </summary>
    public UserDefinedType(IToken tok, string name, TopLevelDecl cd, [Captured] List<Type> typeArgs, List<IToken> moduleName) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cd != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(moduleName == null || cce.NonNullElements(moduleName));
      this.tok = tok;
      this.Name = name;
      this.ResolvedClass = cd;
      this.TypeArgs = typeArgs;
      if (moduleName != null)
        this.Path = moduleName;
      else
        this.Path = new List<IToken>();
    }

    /// <summary>
    /// This constructor constructs a resolved type parameter
    /// </summary>
    public UserDefinedType(IToken tok, string name, TypeParameter tp) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(tp != null);
      this.tok = tok;
      this.Name = name;
      this.TypeArgs = new List<Type>();
      this.ResolvedParam = tp;
      this.Path = new List<IToken>();
    }

    /// <summary>
    /// This constructor constructs a resolved type parameter
    /// </summary>
    public UserDefinedType(TypeParameter tp)
      : this(tp.tok, tp.Name, tp)
    {
      Contract.Requires(tp != null);
    }

    public override bool Equals(Type that) {
      var i = NormalizeExpand();
      if (i is UserDefinedType) {
        var ii = (UserDefinedType)i;
        var t = that.NormalizeExpand() as UserDefinedType;
        if (ii.ResolvedParam != null) {
          return t != null && t.ResolvedParam == ii.ResolvedParam;
        } else if (t == null || ii.ResolvedClass != t.ResolvedClass || ii.TypeArgs.Count != t.TypeArgs.Count) {
          return false;
        } else {
          for (int j = 0; j < ii.TypeArgs.Count; j++) {
            if (!ii.TypeArgs[j].Equals(t.TypeArgs[j])) {
              return false;
            }
          }
          return true;
        }
      } else {
        return i.Equals(that);
      }
    }

    /// <summary>
    /// If type denotes a resolved class type, then return that class type.
    /// Otherwise, return null.
    /// </summary>
    public static UserDefinedType DenotesClass(Type type) {
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<UserDefinedType>() == null || Contract.Result<UserDefinedType>().ResolvedClass is ClassDecl);
      type = type.NormalizeExpand();
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
    public override string TypeName(ModuleDefinition context) {
      Contract.Ensures(Contract.Result<string>() != null);
      if (BuiltIns.IsTupleTypeName(Name)) {
        return "(" + Util.Comma(",", TypeArgs, ty => ty.TypeName(context)) + ")";
      } else {
#if TEST_TYPE_SYNONYM_TRANSPARENCY
        if (Name == "type#synonym#transparency#test" && ResolvedClass is TypeSynonymDecl) {
          return ((TypeSynonymDecl)ResolvedClass).Rhs.TypeName(context);
        }
#endif
        string s = "";
        foreach (var t in Path) {
          if (context != null && t == context.tok) {
            // drop the prefix up to here
            s = "";
          } else {
            s += t.val + ".";
          }
        }
        s += Name;
        if (TypeArgs.Count != 0) {
          s += "<" + Util.Comma(",", TypeArgs, ty => ty.TypeName(context)) + ">";
        }
        return s;
      }
    }

    public override bool SupportsEquality {
      get {
        if (ResolvedClass is ClassDecl || ResolvedClass is NewtypeDecl) {
          return true;
        } else if (ResolvedClass is CoDatatypeDecl) {
          return false;
        } else if (ResolvedClass is IndDatatypeDecl) {
          var dt = (IndDatatypeDecl)ResolvedClass;
          Contract.Assume(dt.EqualitySupport != IndDatatypeDecl.ES.NotYetComputed);
          if (dt.EqualitySupport == IndDatatypeDecl.ES.Never) {
            return false;
          }
          Contract.Assert(dt.TypeArgs.Count == TypeArgs.Count);
          var i = 0;
          foreach (var tp in dt.TypeArgs) {
            if (tp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype && !TypeArgs[i].SupportsEquality) {
              return false;
            }
            i++;
          }
          return true;
        } else if (ResolvedClass is TypeSynonymDecl) {
          var t = (TypeSynonymDecl)ResolvedClass;
          return t.RhsWithArgument(TypeArgs).SupportsEquality;
        } else if (ResolvedParam != null) {
          return ResolvedParam.MustSupportEquality;
        }
        Contract.Assume(false);  // the SupportsEquality getter requires the Type to have been successfully resolved
        return true;
      }
    }
  }

  public abstract class TypeProxy : Type {
    public Type T;  // filled in during resolution
    internal TypeProxy() {
    }

    [Pure]
    public override string TypeName(ModuleDefinition context) {
      Contract.Ensures(Contract.Result<string>() != null);

      return T == null ? "?" : T.TypeName(context);
    }
    public override bool SupportsEquality {
      get {
        if (T != null) {
          return T.SupportsEquality;
        } else {
          return base.SupportsEquality;
        }
      }
    }
    public override bool Equals(Type that) {
      var i = NormalizeExpand();
      if (i is TypeProxy) {
        var u = that.NormalizeExpand() as TypeProxy;
        return u != null && object.ReferenceEquals(i, u);
      } else {
        return i.Equals(that);
      }
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
    public TypeParameter orig;
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
    public readonly bool Co;  // false means only inductive datatypes; true means only co-inductive datatypes
    public readonly bool TypeVariableOK;
    public DatatypeProxy(bool co, bool typeVariableOk = false) {
      Co = co;
      TypeVariableOK = typeVariableOk;
    }
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
  /// This proxy stands for:
  ///     set(Arg) or multiset(Arg) or seq(Arg) or map(Arg, anyRange)
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
        return 2;
      }
    }
  }

  /// <summary>
  /// This proxy can stand for any numeric type.
  /// In addition, if AllowSeq, then it can stand for a seq.
  /// In addition, if AllowSetVarieties, it can stand for a set or multiset.
  /// </summary>
  public class OperationTypeProxy : RestrictedTypeProxy {
    public readonly bool AllowInts;
    public readonly bool AllowReals;
    public readonly bool AllowChar;
    public readonly bool AllowSeq;
    public readonly bool AllowSetVarieties;
    public bool JustInts {
      get { return AllowInts && !AllowReals && !AllowChar && !AllowSeq && !AllowSetVarieties; }
    }
    public bool JustReals {
      get { return !AllowInts && AllowReals && !AllowChar && !AllowSeq && !AllowSetVarieties; }
    }
    public OperationTypeProxy(bool allowInts, bool allowReals, bool allowChar, bool allowSeq, bool allowSetVarieties) {
      Contract.Requires(allowInts || allowReals || allowChar || allowSeq || allowSetVarieties);  // don't allow unsatisfiable constraint
      Contract.Requires(!(!allowInts && !allowReals && allowChar && !allowSeq && !allowSetVarieties));  // to constrain to just char, don't use a proxy
      AllowInts = allowInts;
      AllowReals = allowReals;
      AllowChar = allowChar;
      AllowSeq = allowSeq;
      AllowSetVarieties = allowSetVarieties;
    }
    public override int OrderID {
      get {
        return 3;
      }
    }
    [Pure]
    public override string TypeName(ModuleDefinition context) {
      Contract.Ensures(Contract.Result<string>() != null);

      if (T == null) {
        if (JustInts) {
          return "int";
        } else if (JustReals) {
          return "real";
        }
      }
      return base.TypeName(context);
    }
  }

  /// <summary>
  /// Domain and Range refer to the types of the indexing operation.  That is, in A[i],
  /// i is of type Domain and A[i] is of type Range.
  /// Arg is either Domain or Range, depending on what type it is.  Arg is the type
  /// one would use in an expression "x in C", whereas
  /// This proxy stands for one of:
  ///   seq(T)       Domain,Range,Arg := integer,T,T
  ///   multiset(T)  Domain,Range,Arg := T,integer,T
  ///   if AllowMap, may also be:
  ///   map(T,U)     Domain,Range,Arg := T,U,T
  ///   if AllowArray, may also be:
  ///   array(T)     Domain,Range,Arg := integer,T,T
  /// where "integer" refers to any integer-based numeric type.
  /// </summary>
  public class IndexableTypeProxy : RestrictedTypeProxy {
    public readonly bool AllowMap;
    public readonly bool AllowArray;
    public readonly Type Domain, Range, Arg;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Domain != null);
      Contract.Invariant(Range != null);
      Contract.Invariant(Arg != null);
    }

    public IndexableTypeProxy(Type domain, Type range, Type arg, bool allowMap, bool allowArray) {
      Contract.Requires(domain != null);
      Contract.Requires(range != null);
      Contract.Requires(arg != null);
      Domain = domain;
      Range = range;
      Arg = arg;
      AllowMap = allowMap;
      AllowArray = allowArray;
    }
    public override int OrderID {
      get {
        return 4;
      }
    }
  }

  // ------------------------------------------------------------------------------------------------------

  public abstract class Declaration : IUniqueNameGenerator {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
      Contract.Invariant(Name != null);
    }

    public IToken tok;
    public IToken BodyStartTok = Token.NoToken;
    public IToken BodyEndTok = Token.NoToken;
    public readonly string Name;
    string compileName;
    public virtual string CompileName {
      get {
        if (compileName == null) {
          compileName = NonglobalVariable.CompilerizeName(Name);
        }
        return compileName;
      }
    }
    public Attributes Attributes;  // readonly, except during class merging in the refinement transformations

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

    int nameCount;

    public int GenerateId(string name)
    {
      return nameCount++;
    }
  }

  public class OpaqueType_AsParameter : TypeParameter
  {
    public readonly List<TypeParameter> TypeArgs;
    public OpaqueType_AsParameter(IToken tok, string name, EqualitySupportValue equalitySupport, List<TypeParameter> typeArgs)
      : base(tok, name, equalitySupport)
    {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(typeArgs != null);
      TypeArgs = typeArgs;
    }
  }

  public class TypeParameter : Declaration {
    public interface ParentType {
      string FullName {
        get;
      }
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
        Contract.Requires(value is TopLevelDecl || value is Function || value is Method || value is DatatypeCtor || value is QuantifierExpr);
        //modifies parent;
        parent = value;
      }
    }
    public enum EqualitySupportValue { Required, InferredRequired, Unspecified }
    public EqualitySupportValue EqualitySupport;  // the resolver may change this value from Unspecified to InferredRequired (for some signatures that may immediately imply that equality support is required)
    public bool MustSupportEquality {
      get { return EqualitySupport != EqualitySupportValue.Unspecified; }
    }

    public bool NecessaryForEqualitySupportOfSurroundingInductiveDatatype = false;  // computed during resolution; relevant only when Parent denotes an IndDatatypeDecl

    public bool IsAbstractTypeDeclaration { // true if this type parameter represents t in type t;
      get { return parent == null; }
    }
    public bool IsToplevelScope { // true if this type parameter is on a toplevel (ie. class C<T>), and false if it is on a member (ie. method m<T>(...))
      get { return parent is TopLevelDecl; }
    }
    public int PositionalIndex; // which type parameter this is (ie. in C<S, T, U>, S is 0, T is 1 and U is 2).

    public TypeParameter(IToken tok, string name, EqualitySupportValue equalitySupport = EqualitySupportValue.Unspecified)
      : base(tok, name, null) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      EqualitySupport = equalitySupport;
    }

    public TypeParameter(IToken tok, string name, int positionalIndex, ParentType parent)
       : this(tok, name)
    {
      PositionalIndex = positionalIndex;
      Parent = parent;
    }

    public string FullName() {
      // when debugging, print it all:
      return /* Parent.FullName + "." + */ Name;
    }
  }

  // Represents a submodule declaration at module level scope
  abstract public class ModuleDecl : TopLevelDecl
  {
    public ModuleSignature Signature; // filled in by resolution, in topological order.
    public int Height;
    public readonly bool Opened;
    public ModuleDecl(IToken tok, string name, ModuleDefinition parent, bool opened)
      : base(tok, name, parent, new List<TypeParameter>(), null) {
        Height = -1;
      Signature = null;
      Opened = opened;
    }
  }
  // Represents module X { ... }
  public class LiteralModuleDecl : ModuleDecl
  {
    public readonly ModuleDefinition ModuleDef;
    public LiteralModuleDecl(ModuleDefinition module, ModuleDefinition parent)
      : base(module.tok, module.Name, parent, false) {
      ModuleDef = module;
    }
  }
  // Represents "module name = path;", where name is a identifier and path is a possibly qualified name.
  public class AliasModuleDecl : ModuleDecl
  {
    public ModuleDecl ModuleReference; // should refer to another declaration somewhere. NOTE: cyclicity is possible, and should
                                       // be detected and warned.
    public readonly List<IToken> Path; // generated by the parser, this is looked up
    public ModuleDecl Root;            // the moduleDecl that Path[0] refers to.
    public AliasModuleDecl(List<IToken> path, IToken name, ModuleDefinition parent, bool opened)
      : base(name, name.val, parent, opened) {
       Contract.Requires(path != null && path.Count > 0);
       Path = path;
       ModuleReference = null;
    }
  }
  // Represents "module name as path [ = compilePath];", where name is a identifier and path is a possibly qualified name.
  public class ModuleFacadeDecl : ModuleDecl
  {
    public ModuleDecl Root;
    public readonly List<IToken> Path;
    public ModuleDecl CompileRoot;
    public readonly List<IToken> CompilePath;
    public ModuleSignature OriginalSignature;

    public ModuleFacadeDecl(List<IToken> path, IToken name, ModuleDefinition parent, List<IToken> compilePath, bool opened)
      : base(name, name.val, parent, opened) {
      Path = path;
      Root = null;
      CompilePath = compilePath;
    }
  }

  public class ModuleSignature {

    public readonly Dictionary<string, TopLevelDecl> TopLevels = new Dictionary<string, TopLevelDecl>();
    public readonly Dictionary<string, Tuple<DatatypeCtor, bool>> Ctors = new Dictionary<string, Tuple<DatatypeCtor, bool>>();
    public readonly Dictionary<string, MemberDecl> StaticMembers = new Dictionary<string, MemberDecl>();
    public ModuleDefinition ModuleDef = null; // Note: this is null if this signature does not correspond to a specific definition (i.e.
                                              // it is abstract). Otherwise, it points to that definition.
    public ModuleSignature CompileSignature = null; // This is the version of the signature that should be used at compile time.
    public ModuleSignature Refines = null;
    public bool IsGhost = false;
    public ModuleSignature() {}

    public bool FindSubmodule(string name, out ModuleSignature pp) {
      TopLevelDecl top;
      pp = null;
      if (TopLevels.TryGetValue(name, out top)) {
        if (top is ModuleDecl) {
          pp = ((ModuleDecl)top).Signature;
          return true;
        } else return false;
      } else return false;
    }


  }
  public class ModuleDefinition : TopLevelDecl {
    public readonly List<IToken> RefinementBaseName;  // null if no refinement base
    public ModuleDecl RefinementBaseRoot; // filled in early during resolution, corresponds to RefinementBaseName[0]
    public ModuleDefinition RefinementBase;  // filled in during resolution (null if no refinement base)
    public List<Include> Includes;

    public readonly List<TopLevelDecl> TopLevelDecls = new List<TopLevelDecl>();  // filled in by the parser; readonly after that
    public readonly Graph<ICallable> CallGraph = new Graph<ICallable>();  // filled in during resolution
    public int Height;  // height in the topological sorting of modules; filled in during resolution
    public readonly bool IsAbstract;
    public readonly bool IsFacade; // True iff this module represents a module facade (that is, an abstract interface)
    private readonly bool IsBuiltinName; // true if this is something like _System that shouldn't have it's name mangled.
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(TopLevelDecls));
      Contract.Invariant(CallGraph != null);
    }

    public ModuleDefinition(IToken tok, string name, bool isAbstract, bool isFacade, List<IToken> refinementBase, ModuleDefinition parent, Attributes attributes, bool isBuiltinName)
      : base(tok, name, parent, new List<TypeParameter>(), attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      RefinementBaseName = refinementBase;
      IsAbstract = isAbstract;
      IsFacade = isFacade;
      RefinementBaseRoot = null;
      RefinementBase = null;
      Includes = new List<Include>();
      IsBuiltinName = isBuiltinName;
    }
    public virtual bool IsDefaultModule {
      get {
        return false;
      }
    }
    string compileName;
    new public string CompileName {
      get {
        if (compileName == null) {
          if (IsBuiltinName)
            compileName = Name;
          else
            compileName = "_" + Height.ToString() + "_" + NonglobalVariable.CompilerizeName(Name);
        }
        return compileName;
      }
    }

    /// <summary>
    /// Determines if "a" and "b" are in the same strongly connected component of the call graph, that is,
    /// if "a" and "b" are mutually recursive.
    /// Assumes that CallGraph has already been filled in for the modules containing "a" and "b".
    /// </summary>
    public static bool InSameSCC(ICallable a, ICallable b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      var module = a.EnclosingModule;
      return module == b.EnclosingModule && module.CallGraph.GetSCCRepresentative(a) == module.CallGraph.GetSCCRepresentative(b);
    }

    /// <summary>
    /// Return the representative elements of the SCCs that contain contain any member declaration in a
    /// class in "declarations".
    /// Note, the representative element may in some cases be a Method, not necessarily a Function.
    /// </summary>
    public static IEnumerable<ICallable> AllFunctionSCCs(List<TopLevelDecl> declarations) {
      var set = new HashSet<ICallable>();
      foreach (var d in declarations) {
        var cl = d as ClassDecl;
        if (cl != null) {
          var module = cl.Module;
          foreach (var member in cl.Members) {
            var fn = member as Function;
            if (fn != null) {
              var repr = module.CallGraph.GetSCCRepresentative(fn);
              set.Add(repr);
            }
          }
        }
      }
      return set;
    }

    public static IEnumerable<Function> AllFunctions(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        var cl = d as ClassDecl;
        if (cl != null) {
          foreach (var member in cl.Members) {
            var fn = member as Function;
            if (fn != null) {
              yield return fn;
            }
          }
        }
      }
    }

    /// <summary>
    /// Yields all functions and methods that are members of some class in the given list of
    /// declarations.
    /// Note, an iterator declaration is a class, in this sense.
    /// Note, if the given list are the top-level declarations of a module, the yield will include
    /// colemmas but not their associated prefix lemmas (which are tucked into the colemma's
    /// .PrefixLemma field).
    /// </summary>
    public static IEnumerable<ICallable> AllCallables(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        var cl = d as ClassDecl;
        if (cl != null) {
          foreach (var member in cl.Members) {
            var clbl = member as ICallable;
            if (clbl != null) {
              yield return clbl;
            }
          }
        }
      }
    }

    /// <summary>
    /// Yields all functions and methods that are members of some non-iterator class in the given
    /// list of declarations, as well as any IteratorDecl's in that list.
    /// </summary>
    public static IEnumerable<ICallable> AllItersAndCallables(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        if (d is IteratorDecl) {
          var iter = (IteratorDecl)d;
          yield return iter;
        } else if (d is ClassDecl) {
          var cl = (ClassDecl)d;
          foreach (var member in cl.Members) {
            var clbl = member as ICallable;
            if (clbl != null) {
              yield return clbl;
            }
          }
        }
      }
    }

    public static IEnumerable<IteratorDecl> AllIteratorDecls(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        var iter = d as IteratorDecl;
        if (iter != null) {
          yield return iter;
        }
      }
    }

      public static IEnumerable<CoLemma> AllCoLemmas(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        var cl = d as ClassDecl;
        if (cl != null) {
          foreach (var member in cl.Members) {
            var m = member as CoLemma;
            if (m != null) {
              yield return m;
            }
          }
        }
      }
    }
  }

  public class DefaultModuleDecl : ModuleDefinition {
    public DefaultModuleDecl() : base(Token.NoToken, "_module", false, false, null, null, null, true) {
    }
    public override bool IsDefaultModule {
      get {
        return true;
      }
    }
  }

  public abstract class TopLevelDecl : Declaration, TypeParameter.ParentType {
    public readonly ModuleDefinition Module;
    public readonly List<TypeParameter> TypeArgs;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(TypeArgs));
    }

    public TopLevelDecl(IToken tok, string name, ModuleDefinition module, List<TypeParameter> typeArgs, Attributes attributes)
      : base(tok, name, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Module = module;
      TypeArgs = typeArgs;
    }

    public string FullName {
      get {
        return Module.Name + "." + Name;
      }
    }
    public string FullSanitizedName {
      get {
        return Module.CompileName + "." + CompileName;
      }
    }
    public string FullNameInContext(ModuleDefinition context) {
      if (Module == context) {
        return Name;
      } else {
        return Module.Name + "." + Name;
      }
    }
    public string FullCompileName {
      get {
        return Module.CompileName + ".@" + CompileName;
      }
    }
  }

  public class TraitDecl : ClassDecl
  {
      public bool IsParent { set; get; }
      public TraitDecl(IToken tok, string name, ModuleDefinition module,
        List<TypeParameter> typeArgs, [Captured] List<MemberDecl> members, Attributes attributes)
          : base(tok, name, module, typeArgs, members, attributes, null) { }
  }

  public class ClassDecl : TopLevelDecl {
    public readonly List<MemberDecl> Members;
    public TraitDecl Trait;
    public readonly IToken TraitId;
    public bool HasConstructor;  // filled in (early) during resolution; true iff there exists a member that is a Constructor
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Members));
    }

    public ClassDecl(IToken tok, string name, ModuleDefinition module,
      List<TypeParameter> typeArgs, [Captured] List<MemberDecl> members, Attributes attributes, List<IToken> traitId)
      : base(tok, name, module, typeArgs, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(members));
      Members = members;
      if (traitId != null && traitId.Count > 0)
          TraitId = traitId[0]; //there are at most one inheriting trait at the moment
    }
    public virtual bool IsDefaultClass {
      get {
        return false;
      }
    }
  }

  public class DefaultClassDecl : ClassDecl {
    public DefaultClassDecl(ModuleDefinition module, [Captured] List<MemberDecl> members)
      : base(Token.NoToken, "_default", module, new List<TypeParameter>(), members, null,null) {
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
    public ArrayClassDecl(int dims, ModuleDefinition module, Attributes attrs)
    : base(Token.NoToken, BuiltIns.ArrayClassName(dims), module,
      new List<TypeParameter>(new TypeParameter[]{new TypeParameter(Token.NoToken, "arg")}),
      new List<MemberDecl>(), attrs,null)
    {
      Contract.Requires(1 <= dims);
      Contract.Requires(module != null);

      Dims = dims;
    }
  }

  public class ArrowTypeDecl : ClassDecl
  {
    public readonly int Arity;
    public readonly Function Requires;
    public readonly Function Reads;

    public ArrowTypeDecl(List<TypeParameter> tps, Function req, Function reads, ModuleDefinition module, Attributes attributes)
      : base(Token.NoToken, ArrowType.ArrowTypeName(tps.Count - 1), module, tps,
             new List<MemberDecl> { req, reads }, attributes, null) {
      Contract.Requires(tps != null && 1 <= tps.Count);
      Contract.Requires(req != null);
      Contract.Requires(reads != null);
      Contract.Requires(module != null);
      Arity = tps.Count - 1;
      Requires = req;
      Reads = reads;
      Requires.EnclosingClass = this;
      Reads.EnclosingClass = this;
    }
  }

  public abstract class DatatypeDecl : TopLevelDecl
  {
    public readonly List<DatatypeCtor> Ctors;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Ctors));
      Contract.Invariant(1 <= Ctors.Count);
    }

    public DatatypeDecl(IToken tok, string name, ModuleDefinition module, List<TypeParameter> typeArgs,
      [Captured] List<DatatypeCtor> ctors, Attributes attributes)
      : base(tok, name, module, typeArgs, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ctors));
      Contract.Requires(1 <= ctors.Count);
      Ctors = ctors;
    }
    public bool HasFinitePossibleValues {
      get {
        return (TypeArgs.Count == 0 && Ctors.TrueForAll(ctr => ctr.Formals.Count == 0));
      }
    }
  }

  public class IndDatatypeDecl : DatatypeDecl
  {
    public DatatypeCtor DefaultCtor;  // set during resolution
    public bool[] TypeParametersUsedInConstructionByDefaultCtor;  // set during resolution; has same length as the number of type arguments

    public enum ES { NotYetComputed, Never, ConsultTypeArguments }
    public ES EqualitySupport = ES.NotYetComputed;

    public IndDatatypeDecl(IToken tok, string name, ModuleDefinition module, List<TypeParameter> typeArgs,
      [Captured] List<DatatypeCtor> ctors, Attributes attributes)
      : base(tok, name, module, typeArgs, ctors, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ctors));
      Contract.Requires(1 <= ctors.Count);
    }
  }

  public class TupleTypeDecl : IndDatatypeDecl
  {
    public readonly int Dims;
    /// <summary>
    /// Construct a resolved built-in tuple type with "dim" arguments.  "systemModule" is expected to be the _System module.
    /// </summary>
    public TupleTypeDecl(int dims, ModuleDefinition systemModule)
      : this(systemModule, CreateTypeParameters(dims)) {
      Contract.Requires(0 <= dims);
      Contract.Requires(systemModule != null);
    }
    private TupleTypeDecl(ModuleDefinition systemModule, List<TypeParameter> typeArgs)
      : base(Token.NoToken, BuiltIns.TupleTypeName(typeArgs.Count), systemModule, typeArgs, CreateConstructors(typeArgs), null) {
      Contract.Requires(systemModule != null);
      Contract.Requires(typeArgs != null);
      Dims = typeArgs.Count;
      foreach (var ctor in Ctors) {
        ctor.EnclosingDatatype = this;  // resolve here
        DefaultCtor = ctor;
        TypeParametersUsedInConstructionByDefaultCtor = new bool[typeArgs.Count];
        for (int i = 0; i < typeArgs.Count; i++) {
          TypeParametersUsedInConstructionByDefaultCtor[i] = true;
        }
      }
    }
    private static List<TypeParameter> CreateTypeParameters(int dims) {
      Contract.Requires(0 <= dims);
      var ts = new List<TypeParameter>();
      for (int i = 0; i < dims; i++) {
        ts.Add(new TypeParameter(Token.NoToken, "T" + i));
      }
      return ts;
    }
    private static List<DatatypeCtor> CreateConstructors(List<TypeParameter> typeArgs) {
      Contract.Requires(typeArgs != null);
      var formals = new List<Formal>();
      for (int i = 0; i < typeArgs.Count; i++) {
        var tp = typeArgs[i];
        var f = new Formal(Token.NoToken, i.ToString(), new UserDefinedType(Token.NoToken, tp.Name, tp), true, false);
        formals.Add(f);
      }
      var ctor = new DatatypeCtor(Token.NoToken, BuiltIns.TupleTypeCtorName, formals, null);
      return new List<DatatypeCtor>() { ctor };
    }
  }

  public class CoDatatypeDecl : DatatypeDecl
  {
    public CoDatatypeDecl SscRepr;  // filled in during resolution

    public CoDatatypeDecl(IToken tok, string name, ModuleDefinition module, List<TypeParameter> typeArgs,
      [Captured] List<DatatypeCtor> ctors, Attributes attributes)
      : base(tok, name, module, typeArgs, ctors, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ctors));
      Contract.Requires(1 <= ctors.Count);
    }
  }

  public class DatatypeCtor : Declaration, TypeParameter.ParentType
  {
    public readonly List<Formal> Formals;
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
    public List<DatatypeDestructor> Destructors = new List<DatatypeDestructor>();  // contents filled in during resolution; includes both implicit (not mentionable in source) and explicit destructors

    public DatatypeCtor(IToken tok, string name, [Captured] List<Formal> formals, Attributes attributes)
      : base(tok, name, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(formals));
      this.Formals = formals;
    }

    public string FullName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        Contract.Assume(EnclosingDatatype != null);

        return "#" + EnclosingDatatype.FullName + "." + Name;
      }
    }
  }

  [ContractClass(typeof(UniqueNameGeneratorContracts))]
  public interface IUniqueNameGenerator
  {
    int GenerateId(string name);
  }
  [ContractClassFor(typeof(IUniqueNameGenerator))]
  public abstract class UniqueNameGeneratorContracts : IUniqueNameGenerator
  {
    public int GenerateId(string name) {
      Contract.Requires(name != null);
      throw new NotImplementedException();
    }
  }

  /// <summary>
  /// An ICodeContext is an ICallable or a NoContext.
  /// </summary>
  public interface ICodeContext
  {
    bool IsGhost { get; }
    List<TypeParameter> TypeArgs { get; }
    List<Formal> Ins { get ; }
    ModuleDefinition EnclosingModule { get; }  // to be called only after signature-resolution is complete
    bool MustReverify { get; }
    string FullSanitizedName { get; }
    bool AllowsNontermination { get; }
  }
  /// <summary>
  /// An ICallable is a Function, Method, IteratorDecl, or RedirectingTypeDecl.
  /// </summary>
  public interface ICallable : ICodeContext
  {
    IToken Tok { get; }
    string NameRelativeToModule { get; }
    Specification<Expression> Decreases { get; }
    /// <summary>
    /// The InferredDecreases property says whether or not a process was attempted to provide a default decreases
    /// clause.  If such a process was attempted, even if the resulting decreases clause turned out to be empty,
    /// the property will get the value "true".  This is so that a useful error message can be provided.
    /// </summary>
    bool InferredDecreases { get; set; }
  }
  public class DontUseICallable : ICallable
  {
    public bool IsGhost { get { throw new cce.UnreachableException(); } }
    public List<TypeParameter> TypeArgs { get { throw new cce.UnreachableException(); } }
    public List<Formal> Ins { get { throw new cce.UnreachableException(); } }
    public ModuleDefinition EnclosingModule { get { throw new cce.UnreachableException(); } }
    public bool MustReverify { get { throw new cce.UnreachableException(); } }
    public string FullSanitizedName { get { throw new cce.UnreachableException(); } }
    public bool AllowsNontermination { get { throw new cce.UnreachableException(); } }
    public IToken Tok { get { throw new cce.UnreachableException(); } }
    public string NameRelativeToModule { get { throw new cce.UnreachableException(); } }
    public Specification<Expression> Decreases { get { throw new cce.UnreachableException(); } }
    public bool InferredDecreases {
      get { throw new cce.UnreachableException(); }
      set { throw new cce.UnreachableException(); }
    }
  }
  /// <summary>
  /// An IMethodCodeContext is a Method or IteratorDecl.
  /// </summary>
  public interface IMethodCodeContext : ICallable
  {
    List<Formal> Outs { get; }
    Specification<FrameExpression> Modifies { get; }
  }

  /// <summary>
  /// Applies when we are not inside an ICallable.  In particular, a NoContext is used to resolve the attributes of declarations with no other context.
  /// </summary>
  public class NoContext : ICodeContext
  {
    public readonly ModuleDefinition Module;
    public NoContext(ModuleDefinition module)
    {
      this.Module = module;
    }
    bool ICodeContext.IsGhost { get { return true; } }
    List<TypeParameter> ICodeContext.TypeArgs { get { return new List<TypeParameter>(); } }
    List<Formal> ICodeContext.Ins { get { return new List<Formal>(); } }
    Specification<Expression> Decreases { get { return new Specification<Expression>(null, null); } }
    ModuleDefinition ICodeContext.EnclosingModule { get { return Module; } }
    bool ICodeContext.MustReverify { get { Contract.Assume(false, "should not be called on NoContext"); throw new cce.UnreachableException(); } }
    public string FullSanitizedName { get { Contract.Assume(false, "should not be called on NoContext"); throw new cce.UnreachableException(); } }
    public bool AllowsNontermination { get { Contract.Assume(false, "should not be called on NoContext"); throw new cce.UnreachableException(); } }
  }

  public class IteratorDecl : ClassDecl, IMethodCodeContext
  {
    public readonly List<Formal> Ins;
    public readonly List<Formal> Outs;
    public readonly Specification<FrameExpression> Reads;
    public readonly Specification<FrameExpression> Modifies;
    public readonly Specification<Expression> Decreases;
    public readonly List<MaybeFreeExpression> Requires;
    public readonly List<MaybeFreeExpression> Ensures;
    public readonly List<MaybeFreeExpression> YieldRequires;
    public readonly List<MaybeFreeExpression> YieldEnsures;
    public readonly BlockStmt Body;
    public bool SignatureIsOmitted { get { return SignatureEllipsis != null; } }
    public readonly IToken SignatureEllipsis;
    public readonly List<Field> OutsFields;
    public readonly List<Field> OutsHistoryFields;  // these are the 'xs' variables
    public readonly List<Field> DecreasesFields;  // filled in during resolution
    public SpecialField Member_Modifies;  // filled in during resolution
    public SpecialField Member_Reads;  // filled in during resolution
    public SpecialField Member_New;  // filled in during resolution
    public Constructor Member_Init;  // created during registration phase of resolution; its specification is filled in during resolution
    public Predicate Member_Valid;  // created during registration phase of resolution; its specification is filled in during resolution
    public Method Member_MoveNext;  // created during registration phase of resolution; its specification is filled in during resolution
    public readonly LocalVariable YieldCountVariable;
    public IteratorDecl(IToken tok, string name, ModuleDefinition module, List<TypeParameter> typeArgs,
                        List<Formal> ins, List<Formal> outs,
                        Specification<FrameExpression> reads, Specification<FrameExpression> mod, Specification<Expression> decreases,
                        List<MaybeFreeExpression> requires,
                        List<MaybeFreeExpression> ensures,
                        List<MaybeFreeExpression> yieldRequires,
                        List<MaybeFreeExpression> yieldEnsures,
                        BlockStmt body, Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, module, typeArgs, new List<MemberDecl>(), attributes,null)
    {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(ins != null);
      Contract.Requires(outs != null);
      Contract.Requires(reads != null);
      Contract.Requires(mod != null);
      Contract.Requires(decreases != null);
      Contract.Requires(requires != null);
      Contract.Requires(ensures != null);
      Contract.Requires(yieldRequires != null);
      Contract.Requires(yieldEnsures != null);
      Ins = ins;
      Outs = outs;
      Reads = reads;
      Modifies = mod;
      Decreases = decreases;
      Requires = requires;
      Ensures = ensures;
      YieldRequires = yieldRequires;
      YieldEnsures = yieldEnsures;
      Body = body;
      SignatureEllipsis = signatureEllipsis;

      OutsFields = new List<Field>();
      OutsHistoryFields = new List<Field>();
      DecreasesFields = new List<Field>();

      YieldCountVariable = new LocalVariable(tok, tok, "_yieldCount", new EverIncreasingType(), true);
      YieldCountVariable.type = YieldCountVariable.OptionalType;  // resolve YieldCountVariable here
    }

    /// <summary>
    /// This Dafny type exists only for the purpose of giving the yield-count variable a type, so
    /// that the type can be recognized during translation of Dafny into Boogie.  It represents
    /// an integer component in a "decreases" clause whose order is (\lambda x,y :: x GREATER y),
    /// not the usual (\lambda x,y :: x LESS y AND 0 ATMOST y).
    /// </summary>
    public class EverIncreasingType : BasicType
    {
      [Pure]
      public override string TypeName(ModuleDefinition context) {
        return "_increasingInt";
      }
      public override bool Equals(Type that) {
        return that.NormalizeExpand() is EverIncreasingType;
      }
    }

    bool ICodeContext.IsGhost { get { return false; } }
    List<TypeParameter> ICodeContext.TypeArgs { get { return this.TypeArgs; } }
    List<Formal> ICodeContext.Ins { get { return this.Ins; } }
    List<Formal> IMethodCodeContext.Outs { get { return this.Outs; } }
    Specification<FrameExpression> IMethodCodeContext.Modifies { get { return this.Modifies; } }
    IToken ICallable.Tok { get { return this.tok; } }
    string ICallable.NameRelativeToModule { get { return this.Name; } }
    Specification<Expression> ICallable.Decreases { get { return this.Decreases; } }
    bool _inferredDecr;
    bool ICallable.InferredDecreases {
      set { _inferredDecr = value; }
      get { return _inferredDecr; }
    }
    ModuleDefinition ICodeContext.EnclosingModule { get { return this.Module; } }
    bool ICodeContext.MustReverify { get { return false; } }
    public bool AllowsNontermination {
      get {
        return Contract.Exists(Decreases.Expressions, e => e is WildcardExpr);
      }
    }
  }

  public abstract class MemberDecl : Declaration {
    public readonly bool IsStatic;
    public readonly bool IsGhost;
    public TopLevelDecl EnclosingClass;  // filled in during resolution
    public MemberDecl RefinementBase;  // filled in during the pre-resolution refinement transformation; null if the member is new here
    public bool Inherited;
    public MemberDecl(IToken tok, string name, bool isStatic, bool isGhost, Attributes attributes)
      : base(tok, name, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      IsStatic = isStatic;
      IsGhost = isGhost;
    }
    /// <summary>
    /// Returns className+"."+memberName.  Available only after resolution.
    /// </summary>
    public string FullName {
      get {
        Contract.Requires(EnclosingClass != null);
        Contract.Ensures(Contract.Result<string>() != null);

        return EnclosingClass.FullName + "." + Name;
      }
    }
    public string FullSanitizedName {
      get {
        Contract.Requires(EnclosingClass != null);
        Contract.Ensures(Contract.Result<string>() != null);

        return EnclosingClass.FullSanitizedName + "." + CompileName;
      }
    }
    public string FullNameInContext(ModuleDefinition context) {
      Contract.Requires(EnclosingClass != null);
      Contract.Ensures(Contract.Result<string>() != null);

      return EnclosingClass.FullNameInContext(context) + "." + Name;
    }
    public override string CompileName {
      get {
        var nm = base.CompileName;
        if (this.Name == EnclosingClass.Name) {
          nm = "_" + nm;
        }
        return nm;
      }
    }
    public string FullCompileName {
      get {
        Contract.Requires(EnclosingClass != null);
        Contract.Ensures(Contract.Result<string>() != null);

        return EnclosingClass.FullCompileName + ".@" + CompileName;
      }
    }
  }

  public class Field : MemberDecl {
    public readonly bool IsMutable;  // says whether or not the field can ever change values
    public readonly bool IsUserMutable;  // says whether or not code is allowed to assign to the field (IsUserMutable implies IsMutable)
    public readonly Type Type;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Type != null);
      Contract.Invariant(!IsUserMutable || IsMutable);  // IsUserMutable ==> IsMutable
    }

    public Field(IToken tok, string name, bool isGhost, Type type, Attributes attributes)
      : this(tok, name, isGhost, true, true, type, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
    }

    public Field(IToken tok, string name, bool isGhost, bool isMutable, bool isUserMutable, Type type, Attributes attributes)
      : base(tok, name, false, isGhost, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      Contract.Requires(!isUserMutable || isMutable);
      IsMutable = isMutable;
      IsUserMutable = isUserMutable;
      Type = type;
    }
  }

  public class SpecialField : Field
  {
    public readonly string CompiledName;
    public readonly string PreString;
    public readonly string PostString;
    public SpecialField(IToken tok, string name, string compiledName, string preString, string postString, bool isGhost, bool isMutable, bool isUserMutable, Type type, Attributes attributes)
      : base(tok, name, isGhost, isMutable, isUserMutable, type, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(compiledName != null);
      Contract.Requires(preString != null);
      Contract.Requires(postString != null);
      Contract.Requires(!isUserMutable || isMutable);
      Contract.Requires(type != null);

      CompiledName = compiledName;
      PreString = preString;
      PostString = postString;
    }
  }

  public class DatatypeDestructor : SpecialField
  {
    public readonly DatatypeCtor EnclosingCtor;
    public readonly Formal CorrespondingFormal;

    public DatatypeDestructor(IToken tok, DatatypeCtor enclosingCtor, Formal correspondingFormal, string name, string compiledName, string preString, string postString, bool isGhost, Type type, Attributes attributes)
      : base(tok, name, compiledName, preString, postString, isGhost, false, false, type, attributes)
    {
      Contract.Requires(tok != null);
      Contract.Requires(enclosingCtor != null);
      Contract.Requires(correspondingFormal != null);
      Contract.Requires(name != null);
      Contract.Requires(compiledName != null);
      Contract.Requires(preString != null);
      Contract.Requires(postString != null);
      Contract.Requires(type != null);
      EnclosingCtor = enclosingCtor;
      CorrespondingFormal = correspondingFormal;
    }
  }

  public class OpaqueTypeDecl : TopLevelDecl, TypeParameter.ParentType
  {
    public readonly TypeParameter TheType;
    public TypeParameter.EqualitySupportValue EqualitySupport {
      get { return TheType.EqualitySupport; }
    }
    public bool MustSupportEquality {
      get { return TheType.MustSupportEquality; }
    }
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(TheType != null && Name == TheType.Name);
    }

    public OpaqueTypeDecl(IToken tok, string name, ModuleDefinition module, TypeParameter.EqualitySupportValue equalitySupport, List<TypeParameter> typeArgs, Attributes attributes)
      : base(tok, name, module, typeArgs, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(typeArgs != null);
      TheType = new OpaqueType_AsParameter(tok, name, equalitySupport, TypeArgs);
    }
  }

  public interface RedirectingTypeDecl : ICallable
  {
    string Name { get; }
  }

  public class NewtypeDecl : TopLevelDecl, RedirectingTypeDecl
  {
    public readonly Type BaseType;
    public readonly BoundVar Var;  // can be null (if non-null, then object.ReferenceEquals(Var.Type, BaseType))
    public readonly Expression Constraint;  // is null iff Var is
    public NewtypeDecl(IToken tok, string name, ModuleDefinition module, Type baseType, Attributes attributes)
      : base(tok, name, module, new List<TypeParameter>(), attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(baseType != null);
      BaseType = baseType;
    }
    public NewtypeDecl(IToken tok, string name, ModuleDefinition module, BoundVar bv, Expression constraint, Attributes attributes)
      : base(tok, name, module, new List<TypeParameter>(), attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(bv != null && bv.Type != null);
      BaseType = bv.Type;
      Var = bv;
      Constraint = constraint;
    }

    string RedirectingTypeDecl.Name { get { return Name; } }

    bool ICodeContext.IsGhost { get { return true; } }
    List<TypeParameter> ICodeContext.TypeArgs { get { return new List<TypeParameter>(); } }
    List<Formal> ICodeContext.Ins { get { return new List<Formal>(); } }
    ModuleDefinition ICodeContext.EnclosingModule { get { return Module; } }
    bool ICodeContext.MustReverify { get { return false; } }
    bool ICodeContext.AllowsNontermination { get { return false; } }
    IToken ICallable.Tok { get { return tok; } }
    string ICallable.NameRelativeToModule { get { return Name; } }
    Specification<Expression> ICallable.Decreases {
      get {
        // The resolver checks that a NewtypeDecl sits in its own SSC in the call graph.  Therefore,
        // the question of what its Decreases clause is should never arise.
        throw new cce.UnreachableException();
      }
    }
    bool ICallable.InferredDecreases {
      get { throw new cce.UnreachableException(); }  // see comment above about ICallable.Decreases
      set { throw new cce.UnreachableException(); }  // see comment above about ICallable.Decreases
    }
  }

  public class TypeSynonymDecl : TopLevelDecl, RedirectingTypeDecl
  {
    public readonly Type Rhs;
    public TypeSynonymDecl(IToken tok, string name, List<TypeParameter> typeArgs, ModuleDefinition module, Type rhs, Attributes attributes)
      : base(tok, name, module, typeArgs, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(module != null);
      Contract.Requires(rhs != null);
      Rhs = rhs;
    }
    /// <summary>
    /// Returns the declared .Rhs but with formal type arguments replaced by the given actuals.
    /// </summary>
    public Type RhsWithArgument(List<Type> typeArgs) {
      Contract.Requires(typeArgs != null);
      Contract.Requires(typeArgs.Count == TypeArgs.Count);
      // Instantiate with the actual type arguments
      if (typeArgs.Count == 0) {
        // this optimization seems worthwhile
        return Rhs;
      } else {
        var subst = Resolver.TypeSubstitutionMap(TypeArgs, typeArgs);
        return Resolver.SubstType(Rhs, subst);
      }
    }

    string RedirectingTypeDecl.Name { get { return Name; } }

    bool ICodeContext.IsGhost {
      get {
        // A type synonym does not have any expressions or statements, so the the question of IsGhost should never arise.
        throw new cce.UnreachableException();
      }
    }
    List<TypeParameter> ICodeContext.TypeArgs { get { return TypeArgs; } }
    List<Formal> ICodeContext.Ins { get { return new List<Formal>(); } }
    ModuleDefinition ICodeContext.EnclosingModule { get { return Module; } }
    bool ICodeContext.MustReverify {get { return false; } }
    bool ICodeContext.AllowsNontermination { get { return false; } }
    IToken ICallable.Tok { get { return tok; } }
    string ICallable.NameRelativeToModule { get { return Name; } }
    Specification<Expression> ICallable.Decreases {
      get {
        // The resolver checks that a NewtypeDecl sits in its own SSC in the call graph.  Therefore,
        // the question of what its Decreases clause is should never arise.
        throw new cce.UnreachableException();
      }
    }
    bool ICallable.InferredDecreases {
      get { throw new cce.UnreachableException(); }  // see comment above about ICallable.Decreases
      set { throw new cce.UnreachableException(); }  // see comment above about ICallable.Decreases
    }
  }

  [ContractClass(typeof(IVariableContracts))]
  public interface IVariable {
    string Name {
      get;
    }
    string DisplayName {  // what the user thinks he wrote
      get;
    }
    string UniqueName {
      get;
    }
    bool HasBeenAssignedUniqueName {  // unique names are not assigned until the Translator; if you don't already know if that stage has run, this boolean method will tell you
      get;
    }
    string AssignUniqueName(IUniqueNameGenerator generator);
    string CompileName {
      get;
    }
    Type Type {
      get;
    }
    bool IsMutable {
      get;
    }
    bool IsGhost {
      get;
    }
    IToken Tok {
      get;
    }
  }
  [ContractClassFor(typeof(IVariable))]
  public abstract class IVariableContracts : IVariable {
    public string Name {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public string DisplayName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public string UniqueName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public bool HasBeenAssignedUniqueName {
      get {
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public string CompileName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public Type Type {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
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
    public IToken Tok {
      get {
        Contract.Ensures(Contract.Result<IToken>() != null);
        throw new NotImplementedException();
      }
    }
    public string AssignUniqueName(IUniqueNameGenerator generator)
    {
      Contract.Ensures(Contract.Result<string>() != null);
      throw new NotImplementedException();
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
    public string DisplayName {
      get { return LocalVariable.DisplayNameHelper(this); }
    }
    private string uniqueName;
    public string UniqueName {
      get {
        return uniqueName;
      }
    }
    public bool HasBeenAssignedUniqueName {
      get {
        return uniqueName != null;
      }
    }
    public string AssignUniqueName(IUniqueNameGenerator generator)
    {
      if (uniqueName == null)
      {
        var uniqueId = generator.GenerateId(Name);
        uniqueName = string.Format("{0}#{1}", Name, uniqueId);
        compileName = string.Format("_{0}_{1}", uniqueId, CompilerizeName(name));
      }
      return UniqueName;
    }
    static char[] specialChars = new char[] { '\'', '_', '?', '\\', '#' };
    public static string CompilerizeName(string nm) {
      if ('0' <= nm[0] && nm[0] <= '9') {
        // the identifier is one that consists of just digits
        return "_" + nm;
      }
      string name = null;
      int i = 0;
      while (true) {
        int j = nm.IndexOfAny(specialChars, i);
        if (j == -1) {
          if (i == 0) {
            return nm;  // this is the common case
          } else {
            return name + nm.Substring(i);
          }
        } else {
          string nxt = nm.Substring(i, j - i);
          name = name == null ? nxt : name + nxt;
          switch (nm[j]) {
            case '\'': name += "_k"; break;
            case '_': name += "__"; break;
            case '?': name += "_q"; break;
            case '\\': name += "_b"; break;
            case '#': name += "_h"; break;
            default:
              Contract.Assume(false);  // unexpected character
              break;
          }
          i = j + 1;
          if (i == nm.Length) {
            return name;
          }
        }
      }
    }
    protected string compileName;
    public virtual string CompileName {
      get {
        if (compileName == null)
        {
          compileName = string.Format("_{0}_{1}", Compiler.UniqueNameGeneratorSingleton.GenerateId(Name), CompilerizeName(name));
        }
        return compileName;
      }
    }
    Type type;
    public Type Type {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);
        return type.Normalize();
      }
    }
    public abstract bool IsMutable {
      get;
    }
    bool isGhost;  // readonly after resolution
    public bool IsGhost {
      get {
        return isGhost;
      }
      set {
        isGhost = value;
      }
    }
    public IToken Tok {
      get {
        return tok;
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
  }

  public class Formal : NonglobalVariable {
    public readonly bool InParam;  // true to in-parameter, false for out-parameter
    public override bool IsMutable {
      get {
        return !InParam;
      }
    }

    public Formal(IToken tok, string name, Type type, bool inParam, bool isGhost)
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
    public override string CompileName {
      get {
        if (compileName == null) {
          compileName = CompilerizeName(Name);
        }
        return compileName;
      }
    }
  }

  /// <summary>
  /// An ImplicitFormal is a parameter that is declared implicitly, in particular the "_k" depth parameter
  /// of each colemma (for use in the comethod body only, not the specification).
  /// </summary>
  public class ImplicitFormal : Formal
  {
    public ImplicitFormal(IToken tok, string name, Type type, bool inParam, bool isGhost)
      : base(tok, name, type, inParam, isGhost) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
    }
  }

  /// <summary>
  /// A "ThisSurrogate" is used during translation time to make the treatment of the receiver more similar to
  /// the treatment of other in-parameters.
  /// </summary>
  public class ThisSurrogate : Formal
  {
    public ThisSurrogate(IToken tok, Type type)
      : base(tok, "this", type, true, false) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
    }
  }

  public class BoundVar : NonglobalVariable {
    public override bool IsMutable {
      get {
        return false;
      }
    }

    public BoundVar(IToken tok, string name, Type type)
      : base(tok, name, type, false) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
    }
  }

  public class Function : MemberDecl, TypeParameter.ParentType, ICallable {
    public bool IsRecursive;  // filled in during resolution
    public readonly List<TypeParameter> TypeArgs;
    public readonly List<Formal> Formals;
    public readonly Type ResultType;
    public readonly List<Expression> Req;
    public readonly List<FrameExpression> Reads;
    public readonly List<Expression> Ens;
    public readonly Specification<Expression> Decreases;
    public Expression Body;  // an extended expression; Body is readonly after construction, except for any kind of rewrite that may take place around the time of resolution
    public bool SignatureIsOmitted { get { return SignatureEllipsis != null; } }  // is "false" for all Function objects that survive into resolution
    public readonly IToken SignatureEllipsis;
    public bool IsBuiltin;
    public Function OverriddenFunction;

    public Type Type {
      get {
        // Note, the following returned type can contain type parameters from the function and its enclosing class
        return new ArrowType(tok, Formals.ConvertAll(f => f.Type), ResultType);
      }
    }

    public bool AllowsNontermination {
      get {
        return Contract.Exists(Decreases.Expressions, e => e is WildcardExpr);
      }
    }

    /// <summary>
    /// The "AllCalls" field is used for non-CoPredicate, non-PrefixPredicate functions only (so its value should not be relied upon for CoPredicate and PrefixPredicate functions).
    /// It records all function calls made by the Function, including calls made in the body as well as in the specification.
    /// The field is filled in during resolution (and used toward the end of resolution, to attach a helpful "decreases" prefix to functions in clusters
    /// with co-recursive calls.
    /// </summary>
    public readonly List<FunctionCallExpr> AllCalls = new List<FunctionCallExpr>();
    public enum CoCallClusterInvolvement {
      None,  // the SCC containing the function does not involve any co-recursive calls
      IsMutuallyRecursiveTarget,  // the SCC contains co-recursive calls, and this function is the target of some non-self recursive call
      CoRecursiveTargetAllTheWay,  // the SCC contains co-recursive calls, and this function is the target only of self-recursive calls and co-recursive calls
    }
    public CoCallClusterInvolvement CoClusterTarget = CoCallClusterInvolvement.None;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(TypeArgs));
      Contract.Invariant(cce.NonNullElements(Formals));
      Contract.Invariant(ResultType != null);
      Contract.Invariant(cce.NonNullElements(Req));
      Contract.Invariant(cce.NonNullElements(Reads));
      Contract.Invariant(cce.NonNullElements(Ens));
      Contract.Invariant(Decreases != null);
    }

    /// <summary>
    /// Note, functions are "ghost" by default; a non-ghost function is called a "function method".
    /// </summary>
    public Function(IToken tok, string name, bool isStatic, bool isGhost,
                    List<TypeParameter> typeArgs, List<Formal> formals, Type resultType,
                    List<Expression> req, List<FrameExpression> reads, List<Expression> ens, Specification<Expression> decreases,
                    Expression body, Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, isStatic, isGhost, attributes) {

      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(formals));
      Contract.Requires(resultType != null);
      Contract.Requires(cce.NonNullElements(req));
      Contract.Requires(cce.NonNullElements(reads));
      Contract.Requires(cce.NonNullElements(ens));
      Contract.Requires(decreases != null);
      this.TypeArgs = typeArgs;
      this.Formals = formals;
      this.ResultType = resultType;
      this.Req = req;
      this.Reads = reads;
      this.Ens = ens;
      this.Decreases = decreases;
      this.Body = body;
      this.SignatureEllipsis = signatureEllipsis;
    }

    bool ICodeContext.IsGhost { get { return this.IsGhost; } }
    List<TypeParameter> ICodeContext.TypeArgs { get { return this.TypeArgs; } }
    List<Formal> ICodeContext.Ins { get { return this.Formals; } }
    IToken ICallable.Tok { get { return this.tok; } }
    string ICallable.NameRelativeToModule { get { return EnclosingClass.Name + "." + Name; } }
    Specification<Expression> ICallable.Decreases { get { return this.Decreases; } }
    bool _inferredDecr;
    bool ICallable.InferredDecreases {
      set { _inferredDecr = value; }
      get { return _inferredDecr; }
    }
    ModuleDefinition ICodeContext.EnclosingModule { get { return this.EnclosingClass.Module; } }
    bool ICodeContext.MustReverify { get { return false; } }
  }

  public class Predicate : Function
  {
    public enum BodyOriginKind
    {
      OriginalOrInherited,  // this predicate definition is new (and the predicate may or may not have a body), or the predicate's body (whether or not it exists) is being inherited unmodified (from the previous refinement--it may be that the inherited body was itself an extension, for example)
      DelayedDefinition,  // this predicate declaration provides, for the first time, a body--the declaration refines a previously declared predicate, but the previous one had no body
      Extension  // this predicate extends the definition of a predicate with a body in a module being refined
    }
    public readonly BodyOriginKind BodyOrigin;
    public Predicate(IToken tok, string name, bool isStatic, bool isGhost,
                     List<TypeParameter> typeArgs, List<Formal> formals,
                     List<Expression> req, List<FrameExpression> reads, List<Expression> ens, Specification<Expression> decreases,
                     Expression body, BodyOriginKind bodyOrigin, Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, isStatic, isGhost, typeArgs, formals, new BoolType(), req, reads, ens, decreases, body, attributes, signatureEllipsis) {
      Contract.Requires(bodyOrigin == Predicate.BodyOriginKind.OriginalOrInherited || body != null);
      BodyOrigin = bodyOrigin;
    }
  }

  /// <summary>
  /// An PrefixPredicate is the inductive unrolling P# implicitly declared for every copredicate P.
  /// </summary>
  public class PrefixPredicate : Function
  {
    public readonly Formal K;
    public readonly CoPredicate Co;
    public PrefixPredicate(IToken tok, string name, bool isStatic,
                     List<TypeParameter> typeArgs, Formal k, List<Formal> formals,
                     List<Expression> req, List<FrameExpression> reads, List<Expression> ens, Specification<Expression> decreases,
                     Expression body, Attributes attributes, CoPredicate coPred)
      : base(tok, name, isStatic, true, typeArgs, formals, new BoolType(), req, reads, ens, decreases, body, attributes, null) {
      Contract.Requires(k != null);
      Contract.Requires(coPred != null);
      Contract.Requires(formals != null && 1 <= formals.Count && formals[0] == k);
      K = k;
      Co = coPred;
    }
  }

  public class CoPredicate : Function
  {
    public readonly List<FunctionCallExpr> Uses = new List<FunctionCallExpr>();  // filled in during resolution, used by verifier
    public PrefixPredicate PrefixPredicate;  // filled in during resolution (name registration)

    public CoPredicate(IToken tok, string name, bool isStatic,
                     List<TypeParameter> typeArgs, List<Formal> formals,
                     List<Expression> req, List<FrameExpression> reads, List<Expression> ens,
                     Expression body, Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, isStatic, true, typeArgs, formals, new BoolType(),
             req, reads, ens, new Specification<Expression>(new List<Expression>(), null), body, attributes, signatureEllipsis) {
    }

    /// <summary>
    /// For the given call P(s), return P#[depth](s).  The resulting expression shares some of the subexpressions
    /// with 'fexp' (that is, what is returned is not necessarily a clone).
    /// </summary>
    public FunctionCallExpr CreatePrefixPredicateCall(FunctionCallExpr fexp, Expression depth) {
      Contract.Requires(fexp != null);
      Contract.Requires(fexp.Function == this);
      Contract.Requires(depth != null);
      Contract.Ensures(Contract.Result<FunctionCallExpr>() != null);

      var args = new List<Expression>() { depth };
      args.AddRange(fexp.Args);
      var prefixPredCall = new FunctionCallExpr(fexp.tok, this.PrefixPredicate.Name, fexp.Receiver, fexp.OpenParen, args);
      prefixPredCall.Function = this.PrefixPredicate;  // resolve here

      prefixPredCall.TypeArgumentSubstitutions = new Dictionary<TypeParameter, Type>();
      var old_to_new = new Dictionary<TypeParameter, TypeParameter>();
      for (int i = 0; i < this.TypeArgs.Count; i++) {
	 old_to_new[this.TypeArgs[i]] = this.PrefixPredicate.TypeArgs[i];
      }
      foreach (var p in fexp.TypeArgumentSubstitutions) {
        prefixPredCall.TypeArgumentSubstitutions[old_to_new[p.Key]] = p.Value;
      }  // resolved here.

      prefixPredCall.Type = fexp.Type;  // resolve here
      prefixPredCall.CoCall = fexp.CoCall;  // resolve here
      return prefixPredCall;
    }
  }

  public class Method : MemberDecl, TypeParameter.ParentType, IMethodCodeContext
  {
    public bool SignatureIsOmitted { get { return SignatureEllipsis != null; } }
    public readonly IToken SignatureEllipsis;
    public bool MustReverify;
    public readonly List<TypeParameter> TypeArgs;
    public readonly List<Formal> Ins;
    public readonly List<Formal> Outs;
    public readonly List<MaybeFreeExpression> Req;
    public readonly Specification<FrameExpression> Mod;
    public readonly List<MaybeFreeExpression> Ens;
    public readonly Specification<Expression> Decreases;
    public BlockStmt Body;  // Body is readonly after construction, except for any kind of rewrite that may take place around the time of resolution
    public bool IsRecursive;  // filled in during resolution
    public bool IsTailRecursive;  // filled in during resolution
    public readonly ISet<IVariable> AssignedAssumptionVariables = new HashSet<IVariable>();
    public Method OverriddenMethod;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(TypeArgs));
      Contract.Invariant(cce.NonNullElements(Ins));
      Contract.Invariant(cce.NonNullElements(Outs));
      Contract.Invariant(cce.NonNullElements(Req));
      Contract.Invariant(Mod != null);
      Contract.Invariant(cce.NonNullElements(Ens));
      Contract.Invariant(Decreases != null);
    }

    public Method(IToken tok, string name,
                  bool isStatic, bool isGhost,
                  [Captured] List<TypeParameter> typeArgs,
                  [Captured] List<Formal> ins, [Captured] List<Formal> outs,
                  [Captured] List<MaybeFreeExpression> req, [Captured] Specification<FrameExpression> mod,
                  [Captured] List<MaybeFreeExpression> ens,
                  [Captured] Specification<Expression> decreases,
                  [Captured] BlockStmt body,
                  Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, isStatic, isGhost, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ins));
      Contract.Requires(cce.NonNullElements(outs));
      Contract.Requires(cce.NonNullElements(req));
      Contract.Requires(mod != null);
      Contract.Requires(cce.NonNullElements(ens));
      Contract.Requires(decreases != null);
      this.TypeArgs = typeArgs;
      this.Ins = ins;
      this.Outs = outs;
      this.Req = req;
      this.Mod = mod;
      this.Ens = ens;
      this.Decreases = decreases;
      this.Body = body;
      this.SignatureEllipsis = signatureEllipsis;
      MustReverify = false;
    }

    bool ICodeContext.IsGhost { get { return this.IsGhost; } }
    List<TypeParameter> ICodeContext.TypeArgs { get { return this.TypeArgs; } }
    List<Formal> ICodeContext.Ins { get { return this.Ins; } }
    List<Formal> IMethodCodeContext.Outs { get { return this.Outs; } }
    Specification<FrameExpression> IMethodCodeContext.Modifies { get { return Mod; } }
    IToken ICallable.Tok { get { return this.tok; } }
    string ICallable.NameRelativeToModule { get { return EnclosingClass.Name + "." + Name; } }
    Specification<Expression> ICallable.Decreases { get { return this.Decreases; } }
    bool _inferredDecr;
    bool ICallable.InferredDecreases {
      set { _inferredDecr = value; }
      get { return _inferredDecr; }
    }
    ModuleDefinition ICodeContext.EnclosingModule {
      get {
        Contract.Assert(this.EnclosingClass != null);  // this getter is supposed to be called only after signature-resolution is complete
        return this.EnclosingClass.Module;
      }
    }
    bool ICodeContext.MustReverify { get { return this.MustReverify; } }
    public bool AllowsNontermination {
      get {
        return Contract.Exists(Decreases.Expressions, e => e is WildcardExpr);
      }
    }
  }

  public class Lemma : Method
  {
    public Lemma(IToken tok, string name,
                 bool isStatic,
                 [Captured] List<TypeParameter> typeArgs,
                 [Captured] List<Formal> ins, [Captured] List<Formal> outs,
                 [Captured] List<MaybeFreeExpression> req, [Captured] Specification<FrameExpression> mod,
                 [Captured] List<MaybeFreeExpression> ens,
                 [Captured] Specification<Expression> decreases,
                 [Captured] BlockStmt body,
                 Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, isStatic, true, typeArgs, ins, outs, req, mod, ens, decreases, body, attributes, signatureEllipsis) {
    }
  }

  public class Constructor : Method
  {
    public Constructor(IToken tok, string name,
                  [Captured] List<TypeParameter> typeArgs,
                  [Captured] List<Formal> ins,
                  [Captured] List<MaybeFreeExpression> req, [Captured] Specification<FrameExpression> mod,
                  [Captured] List<MaybeFreeExpression> ens,
                  [Captured] Specification<Expression> decreases,
                  [Captured] BlockStmt body,
                  Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, false, false, typeArgs, ins, new List<Formal>(), req, mod, ens, decreases, body, attributes, signatureEllipsis) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ins));
      Contract.Requires(cce.NonNullElements(req));
      Contract.Requires(mod != null);
      Contract.Requires(cce.NonNullElements(ens));
      Contract.Requires(decreases != null);
    }

    public bool HasName {
      get {
        return Name != "_ctor";
      }
    }
  }

  /// <summary>
  /// A PrefixLemma is the inductive unrolling M# implicitly declared for every colemma M.
  /// </summary>
  public class PrefixLemma : Method
  {
    public readonly Formal K;
    public readonly CoLemma Co;
    public PrefixLemma(IToken tok, string name, bool isStatic,
                       List<TypeParameter> typeArgs, Formal k, List<Formal> ins, List<Formal> outs,
                       List<MaybeFreeExpression> req, Specification<FrameExpression> mod, List<MaybeFreeExpression> ens, Specification<Expression> decreases,
                       BlockStmt body, Attributes attributes, CoLemma co)
      : base(tok, name, isStatic, true, typeArgs, ins, outs, req, mod, ens, decreases, body, attributes, null) {
      Contract.Requires(k != null);
      Contract.Requires(ins != null && 1 <= ins.Count && ins[0] == k);
      Contract.Requires(co != null);
      K = k;
      Co = co;
    }
  }

  public class CoLemma : Method
  {
    public PrefixLemma PrefixLemma;  // filled in during resolution (name registration)

    public CoLemma(IToken tok, string name,
                   bool isStatic,
                   List<TypeParameter> typeArgs,
                   List<Formal> ins, [Captured] List<Formal> outs,
                   List<MaybeFreeExpression> req, [Captured] Specification<FrameExpression> mod,
                   List<MaybeFreeExpression> ens,
                   Specification<Expression> decreases,
                   BlockStmt body,
                   Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, isStatic, true, typeArgs, ins, outs, req, mod, ens, decreases, body, attributes, signatureEllipsis) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ins));
      Contract.Requires(cce.NonNullElements(outs));
      Contract.Requires(cce.NonNullElements(req));
      Contract.Requires(mod != null);
      Contract.Requires(cce.NonNullElements(ens));
      Contract.Requires(decreases != null);
    }
  }

  // ------------------------------------------------------------------------------------------------------

  public abstract class Statement {
    public readonly IToken Tok;
    public readonly IToken EndTok;  // typically a terminating semi-colon or end-curly-brace
    public LList<Label> Labels;  // mutable during resolution

    private Attributes attributes;
    public Attributes Attributes {
      get {
        return attributes;
      }
      set {
        attributes = value;
      }
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Tok != null);
      Contract.Invariant(EndTok != null);
    }

    public bool IsGhost;  // filled in by resolution

    public Statement(IToken tok, IToken endTok, Attributes attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      this.Tok = tok;
      this.EndTok = endTok;
      this.attributes = attrs;
    }

    public Statement(IToken tok, IToken endTok)
      : this(tok, endTok, null) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
    }

    /// <summary>
    /// Returns the non-null substatements of the Statements.
    /// </summary>
    public virtual IEnumerable<Statement> SubStatements {
      get { yield break; }
    }

    /// <summary>
    /// Returns the non-null expressions of this statement proper (that is, do not include the expressions of substatements).
    /// </summary>
    public virtual IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in Attributes.SubExpressions(Attributes)) {
          yield return e;
        }
      }
    }
  }

  public class LList<T>
  {
    public readonly T Data;
    public readonly LList<T> Next;
    const LList<T> Empty = null;

    public LList(T d, LList<T> next) {
      Data = d;
      Next = next;
    }

    public static LList<T> Append(LList<T> a, LList<T> b) {
      if (a == null) return b;
      return new LList<T>(a.Data, Append(a.Next, b));
      // pretend this is ML
    }
    public static int Count(LList<T> n) {
      int count = 0;
      while (n != null) {
        count++;
        n = n.Next;
      }
      return count;
    }
  }

  public class Label
  {
    public readonly IToken Tok;
    public readonly string Name;
    public readonly int UniqueId;
    static int nodes = 0;

    public Label(IToken tok, string label) {
      Contract.Requires(tok != null);
      Tok = tok;
      Name = label;
      UniqueId = nodes++;
    }
  }

  public abstract class PredicateStmt : Statement
  {
    public readonly Expression Expr;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Expr != null);
    }

    public PredicateStmt(IToken tok, IToken endTok, Expression expr, Attributes attrs)
      : base(tok, endTok, attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(expr != null);
      this.Expr = expr;
    }

    public PredicateStmt(IToken tok, IToken endTok, Expression expr)
      : this(tok, endTok, expr, null) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(expr != null);
      this.Expr = expr;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        yield return Expr;
      }
    }
  }

  public class AssertStmt : PredicateStmt {
    public AssertStmt(IToken tok, IToken endTok, Expression expr, Attributes attrs)
      : base(tok, endTok, expr, attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(expr != null);
    }
  }

  public class AssumeStmt : PredicateStmt {
    public AssumeStmt(IToken tok, IToken endTok, Expression expr, Attributes attrs)
      : base(tok, endTok, expr, attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(expr != null);
    }
  }

  public class PrintStmt : Statement {
    public readonly List<Expression> Args;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Args));
    }

    public PrintStmt(IToken tok, IToken endTok, List<Expression> args)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(args));

      Args = args;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var arg in Args) {
          yield return arg;
        }
      }
    }
  }

  public class BreakStmt : Statement {
    public readonly string TargetLabel;
    public readonly int BreakCount;
    public Statement TargetStmt;  // filled in during resolution
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(TargetLabel != null || 1 <= BreakCount);
    }

    public BreakStmt(IToken tok, IToken endTok, string targetLabel)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(targetLabel != null);
      this.TargetLabel = targetLabel;
    }
    public BreakStmt(IToken tok, IToken endTok, int breakCount)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(1 <= breakCount);
      this.BreakCount = breakCount;
    }
  }

  public abstract class ProduceStmt : Statement
  {
    public List<AssignmentRhs> rhss;
    public UpdateStmt hiddenUpdate;
    public ProduceStmt(IToken tok, IToken endTok, List<AssignmentRhs> rhss)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      this.rhss = rhss;
      hiddenUpdate = null;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        if (rhss != null) {
          foreach (var rhs in rhss) {
            foreach (var ee in rhs.SubExpressions) {
              yield return ee;
            }
          }
        }
      }
    }
    public override IEnumerable<Statement> SubStatements {
      get {
        if (rhss != null) {
          foreach (var rhs in rhss) {
            foreach (var s in rhs.SubStatements) {
              yield return s;
            }
          }
        }
      }
    }
  }

  public class ReturnStmt : ProduceStmt
  {
    public bool ReverifyPost;  // set during pre-resolution refinement transformation
    public ReturnStmt(IToken tok, IToken endTok, List<AssignmentRhs> rhss)
      : base(tok, endTok, rhss) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
    }
  }

  public class YieldStmt : ProduceStmt
  {
    public YieldStmt(IToken tok, IToken endTok, List<AssignmentRhs> rhss)
      : base(tok, endTok, rhss) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
    }
  }

  public abstract class AssignmentRhs
  {
    public readonly IToken Tok;

    private Attributes attributes;
    public Attributes Attributes
    {
      get
      {
        return attributes;
      }
      set
      {
        attributes = value;
      }
    }

    public bool HasAttributes()
    {
      return Attributes != null;
    }

    internal AssignmentRhs(IToken tok, Attributes attrs = null) {
      Tok = tok;
      Attributes = attrs;
    }
    public abstract bool CanAffectPreviouslyKnownExpressions { get; }
    /// <summary>
    /// Returns the non-null subexpressions of the AssignmentRhs.
    /// </summary>
    public virtual IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in Attributes.SubExpressions(Attributes)) {
          yield return e;
        }
      }
    }
    /// <summary>
    /// Returns the non-null sub-statements of the AssignmentRhs.
    /// </summary>
    public virtual IEnumerable<Statement> SubStatements{
      get { yield break; }
    }
  }

  public class ExprRhs : AssignmentRhs
  {
    public readonly Expression Expr;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Expr != null);
    }

    public ExprRhs(Expression expr, Attributes attrs = null)
      : base(expr.tok, attrs)
    {
      Contract.Requires(expr != null);
      Expr = expr;
    }
    public override bool CanAffectPreviouslyKnownExpressions { get { return false; } }
    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Expr;
      }
    }
  }

  /// <summary>
  /// A TypeRhs represents one of three things, each having to do with allocating something in the heap:
  ///  * new T[EE]
  ///    This allocates an array of objects of type T (where EE is a list of expression)
  ///  * new C
  ///    This allocates an object of type C
  ///  * new C.Init(EE)
  ///    This allocates an object of type C and then invokes the method/constructor Init on it
  /// There are four ways to construct a TypeRhs syntactically:
  ///  * TypeRhs(T, EE)
  ///      -- represents new T[EE]
  ///  * TypeRhs(C)
  ///      -- represents new C
  ///  * TypeRhs(Path, null, EE)
  ///    Here, Path may either be of the form C.Init
  ///      -- represents new C.Init(EE)
  ///    or all of Path denotes a type
  ///      -- represents new C._ctor(EE), where _ctor is the anonymous constructor for class C
  ///  * TypeRhs(Path, s, EE)
  ///    Here, Path must denote a type and s is a string that denotes the method/constructor Init
  ///      -- represents new Path.s(EE)
  /// </summary>
  public class TypeRhs : AssignmentRhs
  {
    /// <summary>
    /// If ArrayDimensions != null, then the TypeRhs represents "new EType[ArrayDimensions]"
    ///     and Arguments, OptionalNameComponent, and InitCall are all null.
    /// If Arguments == null, then the TypeRhs represents "new C"
    ///     and ArrayDimensions, OptionalNameComponent, and InitCall are all null.
    /// If OptionalNameComponent != null, then the TypeRhs represents "new EType.OptionalNameComponents(Arguments)"
    ///     and InitCall is filled in by resolution, and ArrayDimensions == null and Arguments != null.
    /// If OptionalNameComponent == null and Arguments != null, then the TypeRHS has not been resolved yet;
    ///   resolution will either produce an error or will chop off the last part of "EType" and move it to
    ///   OptionalNameComponent, after which the case above applies.
    /// </summary>
    public Type EType;  // almost readonly, except that resolution can split a given EType into a new EType plus a non-null OptionalNameComponent
    public readonly List<Expression> ArrayDimensions;
    public readonly List<Expression> Arguments;
    public Expression ReceiverArgumentForInitCall;  // may be filled during resolution (and, if so, had better be done before InitCall is filled)
    public string OptionalNameComponent;
    public CallStmt InitCall;  // may be null (and is definitely null for arrays), may be filled in during resolution
    public Type Type;  // filled in during resolution
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(EType != null);
      Contract.Invariant(ArrayDimensions == null || (Arguments == null && OptionalNameComponent == null && InitCall == null));
      Contract.Invariant(ArrayDimensions == null || 1 <= ArrayDimensions.Count);
      Contract.Invariant(OptionalNameComponent == null || (Arguments != null && ArrayDimensions == null));
    }

    public TypeRhs(IToken tok, Type type, List<Expression> arrayDimensions)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(arrayDimensions != null && 1 <= arrayDimensions.Count);
      EType = type;
      ArrayDimensions = arrayDimensions;
    }
    public TypeRhs(IToken tok, Type type)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      EType = type;
    }
    public TypeRhs(IToken tok, Type type, string optionalNameComponent, Expression receiverForInitCall, List<Expression> arguments)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(arguments != null);
      EType = type;
      OptionalNameComponent = optionalNameComponent;  // may be null
      ReceiverArgumentForInitCall = receiverForInitCall;
      Arguments = arguments;
    }
    public override bool CanAffectPreviouslyKnownExpressions {
      get {
        if (InitCall != null) {
          foreach (var mod in InitCall.Method.Mod.Expressions) {
            if (!(mod.E is ThisExpr)) {
              return true;
            }
          }
        }
        return false;
      }
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        if (ArrayDimensions != null) {
          foreach (var e in ArrayDimensions) {
            yield return e;
          }
        }
      }
    }
    public override IEnumerable<Statement> SubStatements {
      get {
        if (InitCall != null) {
          yield return InitCall;
        }
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

    public readonly Expression Receiver;
    public readonly string MethodName;
    public readonly List<Expression> Args;
    public Method Method;  // filled in by resolution

    public CallRhs(IToken tok, Expression receiver, string methodName, List<Expression> args)
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
        foreach (var mod in Method.Mod.Expressions) {
          if (!(mod.E is ThisExpr)) {
            return true;
          }
        }
        return false;
      }
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

  public class HavocRhs : AssignmentRhs {
    public HavocRhs(IToken tok)
      : base(tok)
    {
    }
    public override bool CanAffectPreviouslyKnownExpressions { get { return false; } }
  }

  public class VarDeclStmt : Statement
  {
    public readonly List<LocalVariable> Locals;
    public readonly ConcreteUpdateStatement Update;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Locals));
      Contract.Invariant(Locals.Count != 0);
    }

    public VarDeclStmt(IToken tok, IToken endTok, List<LocalVariable> locals, ConcreteUpdateStatement update)
      : base(tok, endTok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(locals != null);
      Contract.Requires(locals.Count != 0);

      Locals = locals;
      Update = update;
    }

    public override IEnumerable<Statement> SubStatements {
      get { if (Update != null) { yield return Update; } }
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var v in Locals) {
          foreach (var e in Attributes.SubExpressions(v.Attributes)) {
            yield return e;
          }
        }
      }
    }
  }

  /// <summary>
  /// Common superclass of UpdateStmt and AssignSuchThatStmt.
  /// </summary>
  public abstract class ConcreteUpdateStatement : Statement
  {
    public readonly List<Expression> Lhss;
    public ConcreteUpdateStatement(IToken tok, IToken endTok, List<Expression> lhss)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(lhss));
      Lhss = lhss;
    }
  }

  public class AssignSuchThatStmt : ConcreteUpdateStatement
  {
    public readonly Expression Expr;
    public readonly IToken AssumeToken;

    public List<ComprehensionExpr.BoundedPool> Bounds;  // initialized and filled in by resolver; null for a ghost statement
    // invariant Bounds == null || Bounds.Count == BoundVars.Count;
    public List<IVariable> MissingBounds;  // filled in during resolution; remains "null" if bounds can be found
    // invariant Bounds == null || MissingBounds == null;
    public class WiggleWaggleBound : ComprehensionExpr.BoundedPool
    {
      public override bool IsFinite {
        get { return false; }
      }
    }

    /// <summary>
    /// "assumeToken" is allowed to be "null", in which case the verifier will check that a RHS value exists.
    /// If "assumeToken" is non-null, then it should denote the "assume" keyword used in the statement.
    /// </summary>
    public AssignSuchThatStmt(IToken tok, IToken endTok, List<Expression> lhss, Expression expr, IToken assumeToken)
      : base(tok, endTok, lhss) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(lhss));
      Contract.Requires(lhss.Count != 0);
      Contract.Requires(expr != null);
      Expr = expr;
      if (assumeToken != null) {
        AssumeToken = assumeToken;
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        yield return Expr;
        foreach (var lhs in Lhss) {
          yield return lhs;
        }
      }
    }
  }

  public class UpdateStmt : ConcreteUpdateStatement
  {
    public readonly List<AssignmentRhs> Rhss;
    public readonly bool CanMutateKnownState;

    public readonly List<Statement> ResolvedStatements = new List<Statement>();  // contents filled in during resolution
    public override IEnumerable<Statement> SubStatements {
      get { return ResolvedStatements; }
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Lhss));
      Contract.Invariant(cce.NonNullElements(Rhss));
    }
    public UpdateStmt(IToken tok, IToken endTok, List<Expression> lhss, List<AssignmentRhs> rhss)
      : base(tok, endTok, lhss)
    {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(lhss));
      Contract.Requires(cce.NonNullElements(rhss));
      Contract.Requires(lhss.Count != 0 || rhss.Count == 1);
      Rhss = rhss;
      CanMutateKnownState = false;
    }
    public UpdateStmt(IToken tok, IToken endTok, List<Expression> lhss, List<AssignmentRhs> rhss, bool mutate)
      : base(tok, endTok, lhss)
    {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(lhss));
      Contract.Requires(cce.NonNullElements(rhss));
      Contract.Requires(lhss.Count != 0 || rhss.Count == 1);
      Rhss = rhss;
      CanMutateKnownState = mutate;
    }
  }

  public class AssignStmt : Statement {
    public readonly Expression Lhs;
    public readonly AssignmentRhs Rhs;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Lhs != null);
      Contract.Invariant(Rhs != null);
    }

    public AssignStmt(IToken tok, IToken endTok, Expression lhs, AssignmentRhs rhs)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(lhs != null);
      Contract.Requires(rhs != null);
      this.Lhs = lhs;
      this.Rhs = rhs;
    }

    public override IEnumerable<Statement> SubStatements {
      get {
        foreach (var s in Rhs.SubStatements) {
          yield return s;
        }
      }
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        yield return Lhs;
        foreach (var ee in Rhs.SubExpressions) {
          yield return ee;
        }
      }
    }

    /// <summary>
    /// This method assumes "lhs" has been successfully resolved.
    /// </summary>
    public static bool LhsIsToGhost(Expression lhs) {
      Contract.Requires(lhs != null);
      lhs = lhs.Resolved;
      if (lhs is IdentifierExpr) {
        var x = (IdentifierExpr)lhs;
        return x.Var.IsGhost;
      } else if (lhs is MemberSelectExpr) {
        var x = (MemberSelectExpr)lhs;
        return x.Member.IsGhost;
      } else {
        // LHS denotes an array element, which is always non-ghost
        return false;
      }
    }
  }

  public class LocalVariable : IVariable {
    public readonly IToken Tok;
    public readonly IToken EndTok;  // typically a terminating semi-colon or end-curly-brace
    readonly string name;
    public Attributes Attributes;
    public bool IsGhost;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(name != null);
      Contract.Invariant(OptionalType != null);
    }

    public LocalVariable(IToken tok, IToken endTok, string name, Type type, bool isGhost) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);  // can be a proxy, though

      this.Tok = tok;
      this.EndTok = endTok;
      this.name = name;
      this.OptionalType = type;
      this.IsGhost = isGhost;
    }

    public string Name {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return name;
      }
    }
    public static bool HasWildcardName(IVariable v) {
      Contract.Requires(v != null);
      return v.Name.StartsWith("_v");
    }
    public static string DisplayNameHelper(IVariable v) {
      Contract.Requires(v != null);
      return HasWildcardName(v) ? "_" : v.Name;
    }
    public string DisplayName {
      get { return DisplayNameHelper(this); }
    }
    private string uniqueName;
    public string UniqueName {
      get {
        return uniqueName;
      }
    }
    public bool HasBeenAssignedUniqueName {
      get {
        return uniqueName != null;
      }
    }
    public string AssignUniqueName(IUniqueNameGenerator generator)
    {
      if (uniqueName == null)
      {
        var uniqueId = generator.GenerateId(Name);
        uniqueName = string.Format("{0}#{1}", Name, uniqueId);
        compileName = string.Format("_{0}_{1}", uniqueId, NonglobalVariable.CompilerizeName(name));
      }
      return UniqueName;
    }
    string compileName;
    public string CompileName {
      get {
        if (compileName == null)
        {
          compileName = string.Format("_{0}_{1}", Compiler.UniqueNameGeneratorSingleton.GenerateId(Name), NonglobalVariable.CompilerizeName(name));
        }
        return compileName;
      }
    }
    public readonly Type OptionalType;  // this is the type mentioned in the declaration, if any
    internal Type type;  // this is the declared or inferred type of the variable; it is non-null after resolution (even if resolution fails)
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
        return this.IsGhost;
      }
    }
    /// <summary>
    /// This method retrospectively makes the LocalVariable a ghost.  It is to be used only during resolution.
    /// </summary>
    public void MakeGhost() {
      this.IsGhost = true;
    }
    IToken IVariable.Tok {
      get {
        return Tok;
      }
    }
  }

  public class CallStmt : Statement {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      //Contract.Invariant(Receiver != null);
      Contract.Invariant(MethodName != null);
      Contract.Invariant(cce.NonNullElements(Lhs));
      Contract.Invariant(cce.NonNullElements(Args));
      Contract.Invariant(TypeArgumentSubstitutions == null ||
        Contract.ForAll(Method.TypeArgs, tp => TypeArgumentSubstitutions.ContainsKey(tp)));
    }

    public readonly List<Expression> Lhs;
    public Expression Receiver;  // non-null after resolution
    public readonly string MethodName;
    public readonly List<Expression> Args;
    public Dictionary<TypeParameter, Type> TypeArgumentSubstitutions;
	// create, initialized, and used by resolution
        // (could be deleted once all of resolution is done)
	// That's not going to work! It should never be deleted!
    public Method Method;  // filled in by resolution

    public CallStmt(IToken tok, IToken endTok, List<Expression> lhs, Expression receiver, string methodName, List<Expression> args)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(lhs));
      Contract.Requires(receiver != null);
      Contract.Requires(methodName != null);
      Contract.Requires(cce.NonNullElements(args));

      this.Lhs = lhs;
      this.Receiver = receiver;
      this.MethodName = methodName;
      this.Args = args;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var ee in Lhs) {
          yield return ee;
        }
        yield return Receiver;
        foreach (var ee in Args) {
          yield return ee;
        }
      }
    }
  }

  public class BlockStmt : Statement {
    public readonly List<Statement> Body;
    public BlockStmt(IToken tok, IToken endTok, [Captured] List<Statement> body)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(body));
      this.Body = body;
    }

    public override IEnumerable<Statement> SubStatements {
      get { return Body; }
    }
  }

  public class IfStmt : Statement {
    public readonly Expression Guard;
    public readonly BlockStmt Thn;
    public readonly Statement Els;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Thn != null);
      Contract.Invariant(Els == null || Els is BlockStmt || Els is IfStmt || Els is SkeletonStatement);
    }
    public IfStmt(IToken tok, IToken endTok, Expression guard, BlockStmt thn, Statement els)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(thn != null);
      Contract.Requires(els == null || els is BlockStmt || els is IfStmt || els is SkeletonStatement);
      this.Guard = guard;
      this.Thn = thn;
      this.Els = els;
    }
    public override IEnumerable<Statement> SubStatements {
      get {
        yield return Thn;
        if (Els != null) {
          yield return Els;
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        if (Guard != null) {
          yield return Guard;
        }
      }
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
    public AlternativeStmt(IToken tok, IToken endTok, List<GuardedAlternative> alternatives)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(alternatives != null);
      this.Alternatives = alternatives;
    }
    public override IEnumerable<Statement> SubStatements {
      get {
        foreach (var alt in Alternatives) {
          foreach (var s in alt.Body) {
            yield return s;
          }
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var alt in Alternatives) {
          yield return alt.Guard;
        }
      }
    }
  }

  public abstract class LoopStmt : Statement
  {
    public readonly List<MaybeFreeExpression> Invariants;
    public readonly Specification<Expression> Decreases;
    public bool InferredDecreases;  // filled in by resolution
    public readonly Specification<FrameExpression> Mod;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Invariants));
      Contract.Invariant(Decreases != null);
      Contract.Invariant(Mod != null);
    }
    public LoopStmt(IToken tok, IToken endTok, List<MaybeFreeExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod)
    : base(tok, endTok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(invariants));
      Contract.Requires(decreases != null);
      Contract.Requires(mod != null);

      this.Invariants = invariants;
      this.Decreases = decreases;
      this.Mod = mod;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var mfe in Invariants) {
          foreach (var e in Attributes.SubExpressions(mfe.Attributes)) { yield return e; }
          yield return mfe.E;
        }
        foreach (var e in Attributes.SubExpressions(Decreases.Attributes)) { yield return e; }
        if (Decreases.Expressions != null) {
          foreach (var e in Decreases.Expressions) {
            yield return e;
          }
        }
        foreach (var e in Attributes.SubExpressions(Mod.Attributes)) { yield return e; }
        if (Mod.Expressions != null) {
          foreach (var fe in Mod.Expressions) {
            yield return fe.E;
          }
        }
      }
    }
  }

  public class WhileStmt : LoopStmt
  {
    public readonly Expression Guard;
    public readonly BlockStmt Body;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Body != null);
    }

    public WhileStmt(IToken tok, IToken endTok, Expression guard,
                     List<MaybeFreeExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
                     BlockStmt body)
      : base(tok, endTok, invariants, decreases, mod) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(body != null);
      this.Guard = guard;
      this.Body = body;
    }

    public override IEnumerable<Statement> SubStatements {
      get {
        yield return Body;
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        if (Guard != null) {
          yield return Guard;
        }
      }
    }
  }

  /// <summary>
  /// This class is really just a WhileStmt, except that it serves the purpose of remembering if the object was created as the result of a refinement
  /// merge.
  /// </summary>
  public class RefinedWhileStmt : WhileStmt
  {
    public RefinedWhileStmt(IToken tok, IToken endTok, Expression guard,
                            List<MaybeFreeExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
                            BlockStmt body)
      : base(tok, endTok, guard, invariants, decreases, mod, body) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(body != null);
    }
  }

  public class AlternativeLoopStmt : LoopStmt
  {
    public readonly List<GuardedAlternative> Alternatives;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Alternatives != null);
    }
    public AlternativeLoopStmt(IToken tok, IToken endTok,
                               List<MaybeFreeExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
                               List<GuardedAlternative> alternatives)
      : base(tok, endTok, invariants, decreases, mod) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(alternatives != null);
      this.Alternatives = alternatives;
    }
    public override IEnumerable<Statement> SubStatements {
      get {
        foreach (var alt in Alternatives) {
          foreach (var s in alt.Body) {
            yield return s;
          }
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var alt in Alternatives) {
          yield return alt.Guard;
        }
      }
    }
  }

  public class ForallStmt : Statement
  {
    public readonly List<BoundVar> BoundVars;  // note, can be the empty list, in which case Range denotes "true"
    public readonly Expression Range;
    public readonly List<MaybeFreeExpression> Ens;
    public readonly Statement Body;

    public List<ComprehensionExpr.BoundedPool> Bounds;  // initialized and filled in by resolver
    // invariant: if successfully resolved, Bounds.Count == BoundVars.Count;

    /// <summary>
    /// Assign means there are no ensures clauses and the body consists of one update statement,
    ///   either to an object field or to an array.
    /// Call means there are no ensures clauses and the body consists of a single call to a (presumably
    ///   ghost, but non-ghost is also allowed) method with no out-parameters and an empty modifies
    ///   clause.
    /// Proof means there is at least one ensures clause, and the body consists of any (presumably ghost,
    ///   but non-ghost is also allowed) code without side effects on variables (including fields and array
    ///   elements) declared outside the body itself.
    /// Notes:
    /// * More kinds may be allowed in the future.
    /// * One could also allow Call to call non-ghost methods without side effects.  However, that
    ///   would seem pointless in the program, so they are disallowed (to avoid any confusion that
    ///   such use of the forall statement might actually have a point).
    /// * One could allow Proof even without ensures clauses that "export" what was learned.
    ///   However, that might give the false impression that the body is nevertheless exported.
    /// </summary>
    public enum ParBodyKind { Assign, Call, Proof }
    public ParBodyKind Kind;  // filled in during resolution

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(BoundVars != null);
      Contract.Invariant(Range != null);
      Contract.Invariant(BoundVars.Count != 0 || LiteralExpr.IsTrue(Range));
      Contract.Invariant(Ens != null);
    }

    public ForallStmt(IToken tok, IToken endTok, List<BoundVar> boundVars, Attributes attrs, Expression range, List<MaybeFreeExpression> ens, Statement body)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(boundVars));
      Contract.Requires(range != null);
      Contract.Requires(boundVars.Count != 0 || LiteralExpr.IsTrue(range));
      Contract.Requires(cce.NonNullElements(ens));
      this.BoundVars = boundVars;
      this.Attributes = attrs;
      this.Range = range;
      this.Ens = ens;
      this.Body = body;
    }

    public Statement S0 {
      get {
        // dig into Body to find a single statement
        Statement s = this.Body;
        while (true) {
          var block = s as BlockStmt;
          if (block != null && block.Body.Count == 1) {
            s = block.Body[0];
            // dig further into s
          } else if (s is UpdateStmt) {
            var update = (UpdateStmt)s;
            if (update.ResolvedStatements.Count == 1) {
              s = update.ResolvedStatements[0];
              // dig further into s
            } else {
              return s;
            }
          } else {
            return s;
          }
        }
      }
    }

    public override IEnumerable<Statement> SubStatements {
      get {
        if (Body != null) {
          yield return Body;
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        yield return Range;
        foreach (var ee in Ens) {
          foreach (var e in Attributes.SubExpressions(ee.Attributes)) { yield return e; }
          yield return ee.E;
        }
      }
    }
  }

  public class ModifyStmt : Statement
  {
    public readonly Specification<FrameExpression> Mod;
    public readonly BlockStmt Body;

    public ModifyStmt(IToken tok, IToken endTok, List<FrameExpression> mod, Attributes attrs, BlockStmt body)
      : base(tok, endTok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(mod != null);
      Mod = new Specification<FrameExpression>(mod, attrs);
      Body = body;
    }

    public override IEnumerable<Statement> SubStatements {
      get {
        if (Body != null) {
          yield return Body;
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var e in Attributes.SubExpressions(Mod.Attributes)) { yield return e; }
        foreach (var fe in Mod.Expressions) {
          yield return fe.E;
        }
      }
    }
  }

  public class CalcStmt : Statement
  {
    public abstract class CalcOp {
      /// <summary>
      /// Resulting operator "x op z" if "x this y" and "y other z".
      /// Returns null if this and other are incompatible.
      /// </summary>
      [Pure]
      public abstract CalcOp ResultOp(CalcOp other);

      /// <summary>
      /// Returns an expression "line0 this line1".
      /// </summary>
      [Pure]
      public abstract Expression StepExpr(Expression line0, Expression line1);
    }

    public class BinaryCalcOp : CalcOp {
      public readonly BinaryExpr.Opcode Op;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(ValidOp(Op));
      }

      /// <summary>
      /// Is op a valid calculation operator?
      /// </summary>
      [Pure]
      public static bool ValidOp(BinaryExpr.Opcode op) {
        return
             op == BinaryExpr.Opcode.Eq || op == BinaryExpr.Opcode.Neq
          || op == BinaryExpr.Opcode.Lt || op == BinaryExpr.Opcode.Le
          || op == BinaryExpr.Opcode.Gt || op == BinaryExpr.Opcode.Ge
          || LogicOp(op);
      }

      /// <summary>
      /// Is op a valid operator only for Boolean lines?
      /// </summary>
      [Pure]
      public static bool LogicOp(BinaryExpr.Opcode op) {
        return op == BinaryExpr.Opcode.Iff || op == BinaryExpr.Opcode.Imp || op == BinaryExpr.Opcode.Exp;
      }

      public BinaryCalcOp(BinaryExpr.Opcode op) {
        Contract.Requires(ValidOp(op));
        Op = op;
      }

      /// <summary>
      /// Does this subsume other (this . other == other . this == this)?
      /// </summary>
      private bool Subsumes(BinaryCalcOp other) {
        Contract.Requires(other != null);
        var op1 = Op;
        var op2 = other.Op;
        if (op1 == BinaryExpr.Opcode.Neq || op2 == BinaryExpr.Opcode.Neq)
          return op2 == BinaryExpr.Opcode.Eq;
        if (op1 == op2)
          return true;
        if (LogicOp(op1) || LogicOp(op2))
          return op2 == BinaryExpr.Opcode.Eq ||
            (op1 == BinaryExpr.Opcode.Imp && op2 == BinaryExpr.Opcode.Iff) ||
            (op1 == BinaryExpr.Opcode.Exp && op2 == BinaryExpr.Opcode.Iff) ||
            (op1 == BinaryExpr.Opcode.Eq && op2 == BinaryExpr.Opcode.Iff);
        return op2 == BinaryExpr.Opcode.Eq ||
          (op1 == BinaryExpr.Opcode.Lt && op2 == BinaryExpr.Opcode.Le) ||
          (op1 == BinaryExpr.Opcode.Gt && op2 == BinaryExpr.Opcode.Ge);
      }

      public override CalcOp ResultOp(CalcOp other) {
        if (other is BinaryCalcOp) {
          var o = (BinaryCalcOp) other;
          if (this.Subsumes(o)) {
            return this;
          } else if (o.Subsumes(this)) {
            return other;
          }
          return null;
        } else if (other is TernaryCalcOp) {
          return other.ResultOp(this);
        } else {
          Contract.Assert(false);
          throw new cce.UnreachableException();
        }
      }

      public override Expression StepExpr(Expression line0, Expression line1)
      {
        return new BinaryExpr(line0.tok, Op, line0, line1);
      }

      public override string ToString()
      {
        return BinaryExpr.OpcodeString(Op);
      }

    }

    public class TernaryCalcOp : CalcOp {
      public readonly Expression Index; // the only allowed ternary operator is ==#, so we only store the index

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(Index != null);
      }

      public TernaryCalcOp(Expression idx) {
        Contract.Requires(idx != null);
        Index = idx;
      }

      public override CalcOp ResultOp(CalcOp other) {
        if (other is BinaryCalcOp) {
          if (((BinaryCalcOp) other).Op == BinaryExpr.Opcode.Eq) {
            return this;
          }
          return null;
        } else if (other is TernaryCalcOp) {
          var a = Index;
          var b = ((TernaryCalcOp) other).Index;
          var minIndex = new ITEExpr(a.tok, new BinaryExpr(a.tok, BinaryExpr.Opcode.Le, a, b), a, b);
          return new TernaryCalcOp(minIndex); // ToDo: if we could compare expressions for syntactic equalty, we could use this here to optimize
        } else {
          Contract.Assert(false);
          throw new cce.UnreachableException();
        }
      }

      public override Expression StepExpr(Expression line0, Expression line1)
      {
        return new TernaryExpr(line0.tok, TernaryExpr.Opcode.PrefixEqOp, Index, line0, line1);
      }

      public override string ToString()
      {
        return "==#";
      }

    }

    public readonly List<Expression> Lines;  // Last line is dummy, in order to form a proper step with the dangling hint
    public readonly List<BlockStmt> Hints;   // Hints[i] comes after line i; block statement is used as a container for multiple sub-hints
    public readonly CalcOp Op;               // main operator of the calculation
    public readonly List<CalcOp> StepOps;    // StepOps[i] comes after line i
    public CalcOp ResultOp;                  // conclusion operator
    public readonly List<Expression> Steps;  // expressions li op l<i + 1>, filled in during resolution (last step is dummy)
    public Expression Result;                     // expression l0 ResultOp ln, filled in during resolution

    public static readonly CalcOp DefaultOp = new BinaryCalcOp(BinaryExpr.Opcode.Eq);

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Lines != null);
      Contract.Invariant(cce.NonNullElements(Lines));
      Contract.Invariant(Hints != null);
      Contract.Invariant(cce.NonNullElements(Hints));
      Contract.Invariant(Op != null);
      Contract.Invariant(StepOps != null);
      Contract.Invariant(cce.NonNullElements(StepOps));
      Contract.Invariant(ResultOp != null);
      Contract.Invariant(Steps != null);
      Contract.Invariant(cce.NonNullElements(Steps));
      Contract.Invariant(Hints.Count == Math.Max(Lines.Count - 1, 0));
      Contract.Invariant(StepOps.Count == Hints.Count);
    }

    public CalcStmt(IToken tok, IToken endTok, CalcOp op, List<Expression> lines, List<BlockStmt> hints, List<CalcOp> stepOps, CalcOp resultOp)
      : base(tok, endTok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(op != null);
      Contract.Requires(lines != null);
      Contract.Requires(hints != null);
      Contract.Requires(stepOps != null);
      Contract.Requires(cce.NonNullElements(lines));
      Contract.Requires(cce.NonNullElements(hints));
      Contract.Requires(cce.NonNullElements(stepOps));
      Contract.Requires(hints.Count == Math.Max(lines.Count - 1, 0));
      Contract.Requires(stepOps.Count == hints.Count);
      this.Op = op;
      this.Lines = lines;
      this.Hints = hints;
      this.StepOps = stepOps;
      if (resultOp == null) {
        this.ResultOp = stepOps.Aggregate(DefaultOp, (op0, op1) => op0.ResultOp(op1));
      } else {
        this.ResultOp = resultOp;
      }
      this.Steps = new List<Expression>();
      this.Result = null;
    }

    public override IEnumerable<Statement> SubStatements
    {
      get {
        foreach (var h in Hints) {
          yield return h;
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions
    {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var l in Lines) {
          yield return l;
        }
        foreach (var e in Steps) {
          yield return e;
        }
        if (Result != null) {
          yield return Result;
        }
      }
    }

    /// <summary>
    /// Left-hand side of a step expression.
    /// Note that Lhs(op.StepExpr(line0, line1)) != line0 when op is <==.
    /// </summary>
    public static Expression Lhs(Expression step)
    {
      Contract.Requires(step is BinaryExpr || step is TernaryExpr);
      if (step is BinaryExpr) {
        return ((BinaryExpr) step).E0;
      } else {
        return ((TernaryExpr) step).E1;
      }
    }

    /// <summary>
    /// Right-hand side of a step expression.
    /// Note that Rhs(op.StepExpr(line0, line1)) != line1 when op is <==.
    /// </summary>
    public static Expression Rhs(Expression step)
    {
      Contract.Requires(step is BinaryExpr || step is TernaryExpr);
      if (step is BinaryExpr) {
        return ((BinaryExpr) step).E1;
      } else {
        return ((TernaryExpr) step).E2;
      }
    }
  }

  public class MatchStmt : Statement
  {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Source != null);
      Contract.Invariant(cce.NonNullElements(Cases));
      Contract.Invariant(cce.NonNullElements(MissingCases));
    }

    public readonly Expression Source;
    public readonly List<MatchCaseStmt> Cases;
    public readonly List<DatatypeCtor> MissingCases = new List<DatatypeCtor>();  // filled in during resolution
    public readonly bool UsesOptionalBraces;

    public MatchStmt(IToken tok, IToken endTok, Expression source, [Captured] List<MatchCaseStmt> cases, bool usesOptionalBraces)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(source != null);
      Contract.Requires(cce.NonNullElements(cases));
      this.Source = source;
      this.Cases = cases;
      this.UsesOptionalBraces = usesOptionalBraces;
    }

    public override IEnumerable<Statement> SubStatements {
      get {
        foreach (var kase in Cases) {
          foreach (var s in kase.Body) {
            yield return s;
          }
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        yield return Source;
      }
    }
  }

  public class MatchCaseStmt : MatchCase
  {
    public readonly List<Statement> Body;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Body));
    }

    public MatchCaseStmt(IToken tok, string id, [Captured] List<BoundVar> arguments, [Captured] List<Statement> body)
      : base(tok, id, arguments)
    {
      Contract.Requires(tok != null);
      Contract.Requires(id != null);
      Contract.Requires(cce.NonNullElements(arguments));
      Contract.Requires(cce.NonNullElements(body));
      this.Body = body;
    }
  }

  /// <summary>
  /// The class represents several possible scenarios:
  /// * ...;
  ///   S == null
  /// * assert ...
  ///   ConditionOmitted == true
  /// * assume ...
  ///   ConditionOmitted == true
  /// * if ... { Stmt }
  ///   if ... { Stmt } else ElseStmt
  ///   ConditionOmitted == true
  /// * while ... invariant J;
  ///   ConditionOmitted == true && BodyOmitted == true
  /// * while ... invariant J; { Stmt }
  ///   ConditionOmitted == true && BodyOmitted == false
  /// * modify ...;
  ///   ConditionOmitted == true && BodyOmitted == false
  /// * modify ... { Stmt }
  ///   ConditionOmitted == true && BodyOmitted == false
  /// </summary>
  public class SkeletonStatement : Statement
  {
    public readonly Statement S;
    public bool ConditionOmitted { get { return ConditionEllipsis != null; } }
    public readonly IToken ConditionEllipsis;
    public bool BodyOmitted { get { return BodyEllipsis != null; } }
    public readonly IToken BodyEllipsis;
    public readonly List<IToken> NameReplacements;
    public readonly List<Expression> ExprReplacements;
    public SkeletonStatement(IToken tok, IToken endTok)
      : base(tok, endTok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      S = null;
    }
    public SkeletonStatement(Statement s, IToken conditionEllipsis, IToken bodyEllipsis)
      : base(s.Tok, s.EndTok)
    {
      Contract.Requires(s != null);
      S = s;
      ConditionEllipsis = conditionEllipsis;
      BodyEllipsis = bodyEllipsis;
    }
    public SkeletonStatement(IToken tok, IToken endTok, List<IToken> nameReplacements, List<Expression> exprReplacements)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      NameReplacements = nameReplacements;
      ExprReplacements = exprReplacements;

    }
    public override IEnumerable<Statement> SubStatements {
      get {
        // The SkeletonStatement is really a modification of its inner statement S.  Therefore,
        // we don't consider S to be a substatement.  Instead, the substatements of S are the
        // substatements of the SkeletonStatement.  In the case the SkeletonStatement modifies
        // S by omitting its body (which is true only for loops), there are no substatements.
        if (!BodyOmitted) {
          foreach (var s in S.SubStatements) {
            yield return s;
          }
        }
      }
    }
  }

  // ------------------------------------------------------------------------------------------------------

  public abstract class TokenWrapper : IToken
  {
    protected readonly IToken WrappedToken;
    protected TokenWrapper(IToken wrappedToken) {
      Contract.Requires(wrappedToken != null);
      WrappedToken = wrappedToken;
    }

    public int col {
      get { return WrappedToken.col; }
      set { throw new NotSupportedException(); }
    }
    public virtual string filename {
      get { return WrappedToken.filename; }
      set { throw new NotSupportedException(); }
    }
    public bool IsValid {
      get { return WrappedToken.IsValid; }
    }
    public int kind {
      get { return WrappedToken.kind; }
      set { throw new NotSupportedException(); }
    }
    public int line {
      get { return WrappedToken.line; }
      set { throw new NotSupportedException(); }
    }
    public int pos {
      get { return WrappedToken.pos; }
      set { throw new NotSupportedException(); }
    }
    public string val {
      get { return WrappedToken.val; }
      set { throw new NotSupportedException(); }
    }
  }

  public class NestedToken : TokenWrapper
  {
    public NestedToken(IToken outer, IToken inner)
      : base(outer)
    {
      Contract.Requires(outer != null);
      Contract.Requires(inner != null);
      Inner = inner;
    }
    public IToken Outer { get { return WrappedToken; } }
    public readonly IToken Inner;
  }

  /// <summary>
  /// An IncludeToken is a wrapper that indicates that the function/method was
  /// declared in a file that was included. Any proof obligations from such an
  /// included file are to be ignored.
  /// </summary>
  public class IncludeToken : TokenWrapper
  {
    public IncludeToken(IToken wrappedToken)
      : base(wrappedToken) {
      Contract.Requires(wrappedToken != null);
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

    [Pure]
    public bool WasResolved()
    {
      return Type != null;
    }

    public Expression Resolved {
      get {
        Contract.Requires(WasResolved());  // should be called only on resolved expressions; this approximates that precondition
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
      get {
        Contract.Ensures(type != null || Contract.Result<Type>() == null);  // useful in conjunction with postcondition of constructor
        return type == null ? null : type.Normalize();
      }
      set {
        Contract.Requires(!WasResolved());  // set it only once
        Contract.Requires(value != null);
        //modifies type;
        type = value.Normalize();
      }
    }
#if TEST_TYPE_SYNONYM_TRANSPARENCY
    public void DebugTest_ChangeType(Type ty) {
      Contract.Requires(WasResolved());  // we're here to set it again
      Contract.Requires(ty != null);
      type = ty;
    }
#endif

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

    public static IEnumerable<Expression> Conjuncts(Expression expr) {
      Contract.Requires(expr != null);
      Contract.Requires(expr.Type.IsBoolType);
      Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<Expression>>()));

      // strip off parens
      while (true) {
        var pr = expr as ParensExpression;
        if (pr == null) {
          break;
        } else {
          expr = pr.E;
        }
      }

      var bin = expr as BinaryExpr;
      if (bin != null && bin.ResolvedOp == BinaryExpr.ResolvedOpcode.And) {
        foreach (Expression e in Conjuncts(bin.E0)) {
          yield return e;
        }
        foreach (Expression e in Conjuncts(bin.E1)) {
          yield return e;
        }
        yield break;
      }
      yield return expr;
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 + e1"
    /// </summary>
    public static Expression CreateAdd(Expression e0, Expression e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires((e0.Type.IsIntegerType && e1.Type.IsIntegerType) || (e0.Type.IsRealType && e1.Type.IsRealType));
      Contract.Ensures(Contract.Result<Expression>() != null);
      var s = new BinaryExpr(e0.tok, BinaryExpr.Opcode.Add, e0, e1);
      s.ResolvedOp = BinaryExpr.ResolvedOpcode.Add;  // resolve here
      s.Type = e0.Type;  // resolve here
      return s;
    }

    /// <summary>
    /// Create a resolved expression of the form "CVT(e0) - CVT(e1)", where "CVT" is either "int" (if
    /// e0.Type is an integer-based numeric type) or "real" (if e0.Type is a real-based numeric type).
    /// </summary>
    public static Expression CreateSubtract_TypeConvert(Expression e0, Expression e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(
        (e0.Type.IsNumericBased(Type.NumericPersuation.Int) && e1.Type.IsNumericBased(Type.NumericPersuation.Int)) ||
        (e0.Type.IsNumericBased(Type.NumericPersuation.Real) && e1.Type.IsNumericBased(Type.NumericPersuation.Real)));
      Contract.Ensures(Contract.Result<Expression>() != null);

      Type toType = e0.Type.IsNumericBased(Type.NumericPersuation.Int) ? (Type)Type.Int : Type.Real;
      e0 = new ConversionExpr(e0.tok, e0, toType);
      e0.Type = toType;
      e1 = new ConversionExpr(e1.tok, e1, toType);
      e1.Type = toType;
      return CreateSubtract(e0, e1);
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 - e1"
    /// </summary>
    public static Expression CreateSubtract(Expression e0, Expression e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires((e0.Type.IsIntegerType && e1.Type.IsIntegerType) || (e0.Type.IsRealType && e1.Type.IsRealType));
      Contract.Ensures(Contract.Result<Expression>() != null);
      var s = new BinaryExpr(e0.tok, BinaryExpr.Opcode.Sub, e0, e1);
      s.ResolvedOp = BinaryExpr.ResolvedOpcode.Sub;  // resolve here
      s.Type = e0.Type;  // resolve here
      return s;
    }

    /// <summary>
    /// Create a resolved expression of the form "e + n"
    /// </summary>
    public static Expression CreateIncrement(Expression e, int n) {
      Contract.Requires(e != null);
      Contract.Requires(e.Type.IsIntegerType);
      Contract.Requires(0 <= n);
      Contract.Ensures(Contract.Result<Expression>() != null);
      if (n == 0) {
        return e;
      }
      var nn = CreateIntLiteral(e.tok, n);
      return CreateAdd(e, nn);
    }

    /// <summary>
    /// Create a resolved expression of the form "e - n"
    /// </summary>
    public static Expression CreateDecrement(Expression e, int n) {
      Contract.Requires(e != null);
      Contract.Requires(e.Type.IsIntegerType);
      Contract.Requires(0 <= n);
      Contract.Ensures(Contract.Result<Expression>() != null);
      if (n == 0) {
        return e;
      }
      var nn = CreateIntLiteral(e.tok, n);
      return CreateSubtract(e, nn);
    }

    /// <summary>
    /// Create a resolved expression of the form "n"
    /// </summary>
    public static Expression CreateIntLiteral(IToken tok, int n) {
      Contract.Requires(tok != null);
      Contract.Requires(n != int.MinValue);
      if (0 <= n) {
        var nn = new LiteralExpr(tok, n);
        nn.Type = Type.Int;
        return nn;
      } else {
        return CreateDecrement(CreateIntLiteral(tok, 0), -n);
      }
    }

    /// <summary>
    /// Create a resolved expression of the form "x"
    /// </summary>
    public static Expression CreateRealLiteral(IToken tok, Basetypes.BigDec x) {
      Contract.Requires(tok != null);
      var nn = new LiteralExpr(tok, x);
      nn.Type = Type.Real;
      return nn;
    }

    /// <summary>
    /// Create a resolved expression for a bool b
    /// </summary>
    public static Expression CreateBoolLiteral(IToken tok, bool b) {
      Contract.Requires(tok != null);
      var lit = new LiteralExpr(tok, b);
      lit.Type = Type.Bool;  // resolve here
      return lit;
    }

    public static Expression CreateNot(IToken tok, Expression e) {
      Contract.Requires(tok != null);
      Contract.Requires(e.Type.IsBoolType);
      var un = new UnaryOpExpr(tok, UnaryOpExpr.Opcode.Not, e);
      un.Type = Type.Bool;  // resolve here
      return un;
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 LESS e1"
    /// </summary>
    public static Expression CreateLess(Expression e0, Expression e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(e0.Type.IsIntegerType && e1.Type.IsIntegerType);
      Contract.Ensures(Contract.Result<Expression>() != null);
      var s = new BinaryExpr(e0.tok, BinaryExpr.Opcode.Lt, e0, e1);
      s.ResolvedOp = BinaryExpr.ResolvedOpcode.Lt;  // resolve here
      s.Type = Type.Bool;  // resolve here
      return s;
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 ATMOST e1"
    /// </summary>
    public static Expression CreateAtMost(Expression e0, Expression e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires((e0.Type.IsIntegerType && e1.Type.IsIntegerType) || (e0.Type.IsRealType && e1.Type.IsRealType));
      Contract.Ensures(Contract.Result<Expression>() != null);
      var s = new BinaryExpr(e0.tok, BinaryExpr.Opcode.Le, e0, e1);
      s.ResolvedOp = BinaryExpr.ResolvedOpcode.Le;  // resolve here
      s.Type = Type.Bool;  // resolve here
      return s;
    }

    public static Expression CreateEq(Expression e0, Expression e1, Type ty) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(ty != null);
      var eq = new BinaryExpr(e0.tok, BinaryExpr.Opcode.Eq, e0, e1);
      if (ty is SetType) {
        eq.ResolvedOp = BinaryExpr.ResolvedOpcode.SetEq;
      } else if (ty is SeqType) {
        eq.ResolvedOp = BinaryExpr.ResolvedOpcode.SeqEq;
      } else if (ty is MultiSetType) {
        eq.ResolvedOp = BinaryExpr.ResolvedOpcode.InMultiSet;
      } else if (ty is MapType) {
        eq.ResolvedOp = BinaryExpr.ResolvedOpcode.MapEq;
      } else {
        eq.ResolvedOp = BinaryExpr.ResolvedOpcode.EqCommon;
      }
      eq.type = Type.Bool;
      return eq;
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 && e1"
    /// </summary>
    public static Expression CreateAnd(Expression a, Expression b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(a.Type.IsBoolType && b.Type.IsBoolType);
      Contract.Ensures(Contract.Result<Expression>() != null);
      if (LiteralExpr.IsTrue(a)) {
        return b;
      } else if (LiteralExpr.IsTrue(b)) {
        return a;
      } else {
        var and = new BinaryExpr(a.tok, BinaryExpr.Opcode.And, a, b);
        and.ResolvedOp = BinaryExpr.ResolvedOpcode.And;  // resolve here
        and.Type = Type.Bool;  // resolve here
        return and;
      }
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 ==> e1"
    /// </summary>
    public static Expression CreateImplies(Expression a, Expression b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(a.Type.IsBoolType && b.Type.IsBoolType);
      Contract.Ensures(Contract.Result<Expression>() != null);
      if (LiteralExpr.IsTrue(a) || LiteralExpr.IsTrue(b)) {
        return b;
      } else {
        var imp = new BinaryExpr(a.tok, BinaryExpr.Opcode.Imp, a, b);
        imp.ResolvedOp = BinaryExpr.ResolvedOpcode.Imp;  // resolve here
        imp.Type = Type.Bool;  // resolve here
        return imp;
      }
    }

    /// <summary>
    /// Create a resolved expression of the form "if test then e0 else e1"
    /// </summary>
    public static Expression CreateITE(Expression test, Expression e0, Expression e1) {
      Contract.Requires(test != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(test.Type.IsBoolType && e0.Type.Equals(e1.Type));
      Contract.Ensures(Contract.Result<Expression>() != null);
      var ite = new ITEExpr(test.tok, test, e0, e1);
      ite.Type = e0.type;  // resolve here
      return ite;
    }

    /// <summary>
    /// Create a resolved case expression for a match expression
    /// </summary>
    public static MatchCaseExpr CreateMatchCase(MatchCaseExpr old_case, Expression new_body) {
      Contract.Requires(old_case != null);
      Contract.Requires(new_body != null);
      Contract.Ensures(Contract.Result<MatchCaseExpr>() != null);

      ResolvedCloner cloner = new ResolvedCloner();
      var newVars = old_case.Arguments.ConvertAll(cloner.CloneBoundVar);
      new_body = VarSubstituter(old_case.Arguments.ConvertAll<NonglobalVariable>(x=>(NonglobalVariable)x), newVars, new_body);

      var new_case = new MatchCaseExpr(old_case.tok, old_case.Id, newVars, new_body);

      new_case.Ctor = old_case.Ctor; // resolve here
      return new_case;
    }

    /// <summary>
    /// Create a match expression with a resolved type
    /// </summary>
    public static Expression CreateMatch(IToken tok, Expression src, List<MatchCaseExpr> cases, Type type) {
      MatchExpr e = new MatchExpr(tok, src, cases, false);
      e.Type = type;  // resolve here

      return e;
    }

    /// <summary>
    /// Create a let expression with a resolved type and fresh variables
    /// </summary>
    public static Expression CreateLet(IToken tok, List<CasePattern> LHSs, List<Expression> RHSs, Expression body, bool exact) {
      Contract.Requires(tok  != null);
      Contract.Requires(LHSs != null && RHSs != null);
      Contract.Requires(LHSs.Count == RHSs.Count);
      Contract.Requires(body != null);

      ResolvedCloner cloner = new ResolvedCloner();
      var newLHSs = LHSs.ConvertAll(cloner.CloneCasePattern);

      var oldVars = new List<BoundVar>();
      LHSs.Iter(p => oldVars.AddRange(p.Vars));
      var newVars = new List<BoundVar>();
      newLHSs.Iter(p => newVars.AddRange(p.Vars));
      body = VarSubstituter(oldVars.ConvertAll<NonglobalVariable>(x => (NonglobalVariable)x), newVars, body);

      var let = new LetExpr(tok, newLHSs, RHSs, body, exact);
      let.Type = body.Type;  // resolve here
      return let;
    }

    /// <summary>
    /// Create a quantifier expression with a resolved type and fresh variables
    /// Optionally replace the old body with the supplied argument
    /// </summary>
    public static Expression CreateQuantifier(QuantifierExpr expr, bool forall,  Expression body = null) {
      //(IToken tok, List<BoundVar> vars, Expression range, Expression body, Attributes attribs, Qu) {
      Contract.Requires(expr != null);

      ResolvedCloner cloner = new ResolvedCloner();
      var newVars = expr.BoundVars.ConvertAll(cloner.CloneBoundVar);

      if (body == null) {
        body = expr.Term;
      }

      body = VarSubstituter(expr.BoundVars.ConvertAll<NonglobalVariable>(x=>(NonglobalVariable)x), newVars, body);

      QuantifierExpr q;
      if (forall) {
        q = new ForallExpr(expr.tok, new List<TypeParameter>(), newVars, expr.Range, body, expr.Attributes);
      } else {
        q = new ExistsExpr(expr.tok, new List<TypeParameter>(), newVars, expr.Range, body, expr.Attributes);
      }
      q.Type = Type.Bool;

      return q;
    }

    /// <summary>
    /// Create a resolved IdentifierExpr (whose token is that of the variable)
    /// </summary>
    public static Expression CreateIdentExpr(IVariable v) {
      Contract.Requires(v != null);
      var e = new IdentifierExpr(v.Tok, v.Name);
      e.Var = v;  // resolve here
      e.type = v.Type;  // resolve here
      return e;
    }

    public static Expression VarSubstituter(List<NonglobalVariable> oldVars, List<BoundVar> newVars, Expression e) {
      Contract.Requires(oldVars != null && newVars != null);
      Contract.Requires(oldVars.Count == newVars.Count);

      Dictionary<IVariable, Expression/*!*/> substMap = new Dictionary<IVariable, Expression>();
      Dictionary<TypeParameter, Type> typeMap = new Dictionary<TypeParameter, Type>();

      for (int i = 0; i < oldVars.Count; i++) {
        var id = new IdentifierExpr(newVars[i].tok, newVars[i].Name);
        id.Var = newVars[i];    // Resolve here manually
        id.Type = newVars[i].Type;  // Resolve here manually
        substMap.Add(oldVars[i], id);
      }

      Translator.Substituter sub = new Translator.Substituter(null, substMap, typeMap, null);
      return sub.Substitute(e);
    }

    public string AsStringLiteral() {
      var le = this as LiteralExpr;
      if (le != null) {
        return le.Value as string;
      } else {
        return null;
      }
    }
  }

  /// <summary>
  /// Instances of this class are introduced during resolution to indicate that a static method or function has
  /// been invoked without specifying a receiver (that is, by just giving the name of the enclosing class).
  /// </summary>
  public class StaticReceiverExpr : LiteralExpr
  {
    public readonly Type UnresolvedType;

    public StaticReceiverExpr(IToken tok, Type t)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(t != null);
      UnresolvedType = t;
    }

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
      UnresolvedType = Type;
    }
  }

  public class LiteralExpr : Expression {
    /// <summary>
    /// One of the following:
    ///   * 'null' for the 'null' literal (a special case of which is the subclass StaticReceiverExpr)
    ///   * a bool for a bool literal
    ///   * a BigInteger for int literal
    ///   * a Basetypes.BigDec for a (rational) real literal
    ///   * a string for a char literal
    ///     This case always uses the subclass CharLiteralExpr.
    ///     Note, a string is stored to keep any escape sequence, since this simplifies printing of the character
    ///     literal, both when pretty printed as a Dafny expression and when being compiled into C# code.  The
    ///     parser checks the validity of any escape sequence and the verifier deals with turning such into a
    ///     single character value.
    ///   * a string for a string literal
    ///     This case always uses the subclass StringLiteralExpr.
    ///     Note, the string is stored with all escapes as characters.  For example, the input string "hello\n" is
    ///     stored in a LiteralExpr has being 7 characters long, whereas the Dafny (and C#) length of this string is 6.
    ///     This simplifies printing of the string, both when pretty printed as a Dafny expression and when being
    ///     compiled into C# code.  The parser checks the validity of the escape sequences and the verifier deals
    ///     with turning them into single characters.
    /// </summary>
    public readonly object Value;

    [Pure]
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

    public LiteralExpr(IToken tok, Basetypes.BigDec n)
      : base(tok) {
      Contract.Requires(0 <= n.Mantissa.Sign);
      Contract.Requires(tok != null);
      this.Value = n;
    }

    public LiteralExpr(IToken tok, int n)
      :base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(0 <= n);
      this.Value = new BigInteger(n);
    }

    public LiteralExpr(IToken tok, bool b)
      : base(tok) {
      Contract.Requires(tok != null);
      this.Value = b;
    }

    /// <summary>
    /// This constructor is to be used only with the StringLiteralExpr and CharLiteralExpr subclasses, for
    /// two reasons:  both of these literals store a string in .Value, and string literals also carry an
    /// additional field.
    /// </summary>
    protected LiteralExpr(IToken tok, string s)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(s != null);
      this.Value = s;
    }
  }

  public class CharLiteralExpr : LiteralExpr
  {
    public CharLiteralExpr(IToken tok, string s)
      : base(tok, s) {
      Contract.Requires(s != null);
    }
  }

  public class StringLiteralExpr : LiteralExpr
  {
    public readonly bool IsVerbatim;
    public StringLiteralExpr(IToken tok, string s, bool isVerbatim)
      : base(tok, s) {
      Contract.Requires(s != null);
      IsVerbatim = isVerbatim;
    }
  }

  public class DatatypeValue : Expression {
    public readonly string DatatypeName;
    public readonly string MemberName;
    public readonly List<Expression> Arguments;
    public DatatypeCtor Ctor;  // filled in by resolution
    public List<Type> InferredTypeArgs = new List<Type>();  // filled in by resolution
    public bool IsCoCall;  // filled in by resolution
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(DatatypeName != null);
      Contract.Invariant(MemberName != null);
      Contract.Invariant(cce.NonNullElements(Arguments));
      Contract.Invariant(cce.NonNullElements(InferredTypeArgs));
      Contract.Invariant(
	Ctor == null ||
	InferredTypeArgs.Count == Ctor.EnclosingDatatype.TypeArgs.Count);
    }

    public DatatypeValue(IToken tok, string datatypeName, string memberName, [Captured] List<Expression> arguments)
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
  public class ExpressionPair {
    public Expression A, B;
    public ExpressionPair(Expression a, Expression b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      A = a;
      B = b;
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
    public readonly List<Expression> Elements;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Elements));
    }

    public DisplayExpression(IToken tok, List<Expression> elements)
      : base(tok) {
      Contract.Requires(cce.NonNullElements(elements));
      Elements = elements;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { return Elements; }
    }
  }

  public class SetDisplayExpr : DisplayExpression {
    public SetDisplayExpr(IToken tok, List<Expression> elements)
      : base(tok, elements) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(elements));
    }
  }

  public class MultiSetDisplayExpr : DisplayExpression {
    public MultiSetDisplayExpr(IToken tok, List<Expression> elements) : base(tok, elements) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(elements));
    }
  }

  public class MapDisplayExpr : Expression {
    public List<ExpressionPair> Elements;
    public MapDisplayExpr(IToken tok, List<ExpressionPair> elements)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(elements));
      Elements = elements;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var ep in Elements) {
          yield return ep.A;
          yield return ep.B;
        }
      }
    }
  }
  public class SeqDisplayExpr : DisplayExpression {
    public SeqDisplayExpr(IToken tok, List<Expression> elements)
      : base(tok, elements) {
      Contract.Requires(cce.NonNullElements(elements));
      Contract.Requires(tok != null);
    }
  }

  // Former FieldSelectExpression
  public class MemberSelectExpr : Expression {
    public readonly Expression Obj;
    public readonly string MemberName;
    public MemberDecl Member;          // filled in by resolution, will be a Field or Function
    public List<Type> TypeApplication; 
      // If it is a function, it must have all its polymorphic variables applied

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Obj != null);
      Contract.Invariant(MemberName != null);
      Contract.Invariant((Member is Function) == (TypeApplication != null));
    }

    public MemberSelectExpr(IToken tok, Expression obj, string memberName)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(obj != null);
      Contract.Requires(memberName != null);
      this.Obj = obj;
      this.MemberName = memberName;
    }

    public void MemberSelectCase(Action<Field> fieldK, Action<Function> functionK) {
      MemberSelectCase<bool>(
        f => {
          fieldK(f);
          return true;
        },
        f => {
          functionK(f);
          return true;
        });
    }

    public A MemberSelectCase<A>(Func<Field,A> fieldK, Func<Function,A> functionK) {
      var field = Member as Field;
      var function = Member as Function;
      if (field != null) {
        return fieldK(field);
      } else {
        Contract.Assert(function != null);
        return functionK(function);
      }
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
    }

    public SeqSelectExpr(IToken tok, bool selectOne, Expression seq, Expression e0, Expression e1)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(seq != null);
      Contract.Requires(!selectOne || e1 == null);

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
    public Expression ResolvedUpdateExpr;       // May be filled in during resolution

    public SeqUpdateExpr(IToken tok, Expression seq, Expression index, Expression val)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(seq != null);
      Contract.Requires(index != null);
      Contract.Requires(val != null);
      Seq = seq;
      Index = index;
      Value = val;
      ResolvedUpdateExpr = null;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        if (ResolvedUpdateExpr == null)
        {
          yield return Seq;
          yield return Index;
          yield return Value;
        }
        else
        {
          foreach (var e in ResolvedUpdateExpr.SubExpressions)
          {
            yield return e;
          }
        }
      }
    }
  }

  public class ApplyExpr : Expression {
    // The idea is that this apply expression does not need a type argument substitution,
    // since lambda functions and anonymous functions are never polymorphic.
    // Make a FunctionCallExpr otherwise, to call a resolvable anonymous function.
    public readonly Expression Function;
    public readonly List<Expression> Args;
    public readonly IToken OpenParen;

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Function;
        foreach (var e in Args) {
          yield return e;
        }
      }
    }

    public ApplyExpr(IToken tok, IToken openParen, Expression receiver, List<Expression> args) 
      : base(tok)
    {
      OpenParen = openParen;
      Function = receiver;
      Args = args;
    }
  }

  public class FunctionCallExpr : Expression {
    public readonly string Name;
    public readonly Expression Receiver;
    public readonly IToken OpenParen;  // can be null if Args.Count == 0
    public readonly List<Expression> Args;
    public Dictionary<TypeParameter, Type> TypeArgumentSubstitutions;
	// created, initialized, and used by resolution (and also used by translation)
    public enum CoCallResolution {
      No,
      Yes,
      NoBecauseFunctionHasSideEffects,
      NoBecauseFunctionHasPostcondition,
      NoBecauseRecursiveCallsAreNotAllowedInThisContext,
      NoBecauseIsNotGuarded,
      NoBecauseRecursiveCallsInDestructiveContext
    }
    public CoCallResolution CoCall = CoCallResolution.No;  // indicates whether or not the call is a co-recursive call; filled in by resolution

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Name != null);
      Contract.Invariant(Receiver != null);
      Contract.Invariant(cce.NonNullElements(Args));
      Contract.Invariant(
        Function == null || TypeArgumentSubstitutions == null ||
        Contract.ForAll(
          Function.TypeArgs,
        	  a => TypeArgumentSubstitutions.ContainsKey(a)) &&
        Contract.ForAll(
          TypeArgumentSubstitutions.Keys,
        	  a => Function.TypeArgs.Contains(a) || Function.EnclosingClass.TypeArgs.Contains(a)));
    }

    public Function Function;  // filled in by resolution

    [Captured]
    public FunctionCallExpr(IToken tok, string fn, Expression receiver, IToken openParen, [Captured] List<Expression> args)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(fn != null);
      Contract.Requires(receiver != null);
      Contract.Requires(cce.NonNullElements(args));
      Contract.Requires(openParen != null || args.Count == 0);
      Contract.Ensures(type == null);
      Contract.Ensures(cce.Owner.Same(this, receiver));

      this.Name = fn;
      cce.Owner.AssignSame(this, receiver);
      this.Receiver = receiver;
      this.OpenParen = openParen;
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

  public class MultiSetFormingExpr : Expression
  {
    [Peer]
    public readonly Expression E;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
    }

    [Captured]
    public MultiSetFormingExpr(IToken tok, Expression expr)
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

  public abstract class UnaryExpr : Expression
  {
    public readonly Expression E;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
    }

    public UnaryExpr(IToken tok, Expression e)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
      this.E = e;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return E; }
    }
  }

  public class UnaryOpExpr : UnaryExpr
  {
    public enum Opcode {
      Not,
      Cardinality,
      Fresh,
      Lit,  // there is no syntax for this operator, but it is sometimes introduced during translation
    }
    public readonly Opcode Op;

    public UnaryOpExpr(IToken tok, Opcode op, Expression e)
      : base(tok, e) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
      this.Op = op;
    }
  }

  public class ConversionExpr : UnaryExpr
  {
    public readonly Type ToType;
    public ConversionExpr(IToken tok, Expression expr, Type toType)
      : base(tok, expr) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      Contract.Requires(toType != null);
      ToType = toType;
    }
  }

  public class BinaryExpr : Expression
  {
    public enum Opcode {
      Iff,
      Imp,
      Exp, // turned into Imp during resolution
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
      YetUndetermined,  // the value before resolution has determined the value; .ResolvedOp should never be read in this state

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
      // char
      LtChar,
      LeChar,
      GeChar,
      GtChar,
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
      // multi-sets
      MultiSetEq,
      MultiSetNeq,
      MultiSubset,
      MultiSuperset,
      ProperMultiSubset,
      ProperMultiSuperset,
      MultiSetDisjoint,
      InMultiSet,
      NotInMultiSet,
      MultiSetUnion,
      MultiSetIntersection,
      MultiSetDifference,
      // Sequences
      SeqEq,
      SeqNeq,
      ProperPrefix,
      Prefix,
      Concat,
      InSeq,
      NotInSeq,
      // Maps
      MapEq,
      MapNeq,
      InMap,
      NotInMap,
      MapDisjoint,
      MapUnion,
      // datatypes
      RankLt,
      RankGt
    }
    private ResolvedOpcode _theResolvedOp = ResolvedOpcode.YetUndetermined;
    public ResolvedOpcode ResolvedOp {
      set {
        Contract.Assume(_theResolvedOp == ResolvedOpcode.YetUndetermined || _theResolvedOp == value);  // there's never a reason for resolution to change its mind, is there?
        _theResolvedOp = value;
      }
      get {
        Contract.Assume(_theResolvedOp != ResolvedOpcode.YetUndetermined);  // shouldn't read it until it has been properly initialized
        return _theResolvedOp;
      }
    }
    public ResolvedOpcode ResolvedOp_PossiblyStillUndetermined {  // offer a way to return _theResolveOp -- for experts only!
      get { return _theResolvedOp; }
    }
    public static bool IsEqualityOp(ResolvedOpcode op) {
      switch (op) {
        case ResolvedOpcode.EqCommon:
        case ResolvedOpcode.SetEq:
        case ResolvedOpcode.SeqEq:
        case ResolvedOpcode.MultiSetEq:
        case ResolvedOpcode.MapEq:
          return true;
        default:
          return false;
      }
    }

    public static Opcode ResolvedOp2SyntacticOp(ResolvedOpcode rop) {
      switch (rop) {
        case ResolvedOpcode.Iff: return Opcode.Iff;
        case ResolvedOpcode.Imp: return Opcode.Imp;
        case ResolvedOpcode.And: return Opcode.And;
        case ResolvedOpcode.Or: return Opcode.Or;

        case ResolvedOpcode.EqCommon:
        case ResolvedOpcode.SetEq:
        case ResolvedOpcode.MultiSetEq:
        case ResolvedOpcode.SeqEq:
        case ResolvedOpcode.MapEq:
          return Opcode.Eq;

        case ResolvedOpcode.NeqCommon:
        case ResolvedOpcode.SetNeq:
        case ResolvedOpcode.MultiSetNeq:
        case ResolvedOpcode.SeqNeq:
        case ResolvedOpcode.MapNeq:
          return Opcode.Neq;

        case ResolvedOpcode.Lt:
        case ResolvedOpcode.LtChar:
        case ResolvedOpcode.ProperSubset:
        case ResolvedOpcode.ProperMultiSuperset:
        case ResolvedOpcode.ProperPrefix:
        case ResolvedOpcode.RankLt:
          return Opcode.Lt;

        case ResolvedOpcode.Le:
        case ResolvedOpcode.LeChar:
        case ResolvedOpcode.Subset:
        case ResolvedOpcode.MultiSubset:
        case ResolvedOpcode.Prefix:
          return Opcode.Le;

        case ResolvedOpcode.Ge:
        case ResolvedOpcode.GeChar:
        case ResolvedOpcode.Superset:
        case ResolvedOpcode.MultiSuperset:
          return Opcode.Ge;

        case ResolvedOpcode.Gt:
        case ResolvedOpcode.GtChar:
        case ResolvedOpcode.ProperSuperset:
        case ResolvedOpcode.ProperMultiSubset:
        case ResolvedOpcode.RankGt:
          return Opcode.Gt;

        case ResolvedOpcode.Add:
        case ResolvedOpcode.Union:
        case ResolvedOpcode.MultiSetUnion:
        case ResolvedOpcode.MapUnion:
        case ResolvedOpcode.Concat:
          return Opcode.Add;

        case ResolvedOpcode.Sub:
        case ResolvedOpcode.SetDifference:
        case ResolvedOpcode.MultiSetDifference:
          return Opcode.Sub;

        case ResolvedOpcode.Mul:
        case ResolvedOpcode.Intersection:
        case ResolvedOpcode.MultiSetIntersection:
          return Opcode.Mul;

        case ResolvedOpcode.Div: return Opcode.Div;
        case ResolvedOpcode.Mod: return Opcode.Mod;

        case ResolvedOpcode.Disjoint:
        case ResolvedOpcode.MultiSetDisjoint:
        case ResolvedOpcode.MapDisjoint:
          return Opcode.Disjoint;

        case ResolvedOpcode.InSet:
        case ResolvedOpcode.InMultiSet:
        case ResolvedOpcode.InSeq:
        case ResolvedOpcode.InMap:
          return Opcode.In;

        case ResolvedOpcode.NotInSet:
        case ResolvedOpcode.NotInMultiSet:
        case ResolvedOpcode.NotInSeq:
        case ResolvedOpcode.NotInMap:
          return Opcode.NotIn;

        default:
          Contract.Assert(false);  // unexpected ResolvedOpcode
          return Opcode.Add;  // please compiler
      }
    }

    public static string OpcodeString(Opcode op) {
      Contract.Ensures(Contract.Result<string>() != null);

      switch (op) {
        case Opcode.Iff:
          return "<==>";
        case Opcode.Imp:
          return "==>";
        case Opcode.Exp:
          return "<==";
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
      if (op == Opcode.Exp) {
        // The order of operands is reversed so that it can be turned into implication during resolution
        this.E0 = e1;
        this.E1 = e0;
      } else {
        this.E0 = e0;
        this.E1 = e1;
      }
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return E0;
        yield return E1;
      }
    }
  }

  public class TernaryExpr : Expression
  {
    public readonly Opcode Op;
    public readonly Expression E0;
    public readonly Expression E1;
    public readonly Expression E2;
    public enum Opcode { /*SOON: IfOp,*/ PrefixEqOp, PrefixNeqOp }
    public TernaryExpr(IToken tok, Opcode op, Expression e0, Expression e1, Expression e2)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(e2 != null);
      Op = op;
      E0 = e0;
      E1 = e1;
      E2 = e2;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return E0;
        yield return E1;
        yield return E2;
      }
    }
  }

  public class LetExpr : Expression
  {
    public readonly List<CasePattern> LHSs;
    public readonly List<Expression> RHSs;
    public readonly Expression Body;
    public readonly bool Exact;  // Exact==true means a regular let expression; Exact==false means an assign-such-that expression
    public Expression translationDesugaring;  // filled in during translation, lazily; to be accessed only via Translation.LetDesugaring; always null when Exact==true
    public LetExpr(IToken tok, List<CasePattern> lhss, List<Expression> rhss, Expression body, bool exact)
      : base(tok) {
      LHSs = lhss;
      RHSs = rhss;
      Body = body;
      Exact = exact;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var rhs in RHSs) {
          yield return rhs;
        }
        yield return Body;
      }
    }
    public IEnumerable<BoundVar> BoundVars {
      get {
        foreach (var lhs in LHSs) {
          foreach (var bv in lhs.Vars) {
            yield return bv;
          }
        }
      }
    }
  }
  // Represents expr Name: Body
  //         or expr Name: (assert Body == Contract; Body)
  public class NamedExpr : Expression
  {
    public readonly string Name;
    public readonly Expression Body;
    public readonly Expression Contract;
    public readonly IToken ReplacerToken;

    public NamedExpr(IToken tok, string p, Expression body)
      : base(tok) {
      Name = p;
      Body = body;
    }
    public NamedExpr(IToken tok, string p, Expression body, Expression contract, IToken token)
      : base(tok) {
      Name = p;
      Body = body;
      Contract = contract;
      ReplacerToken = token;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Body;
        if (Contract != null) yield return Contract;
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
    public readonly List<BoundVar> BoundVars;
    public readonly Expression Range;
    public readonly Expression Term;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(BoundVars != null);
      Contract.Invariant(Term != null);
    }

    public readonly Attributes Attributes;

    public abstract class BoundedPool {
      public virtual bool IsFinite {
        get { return true; }  // most bounds are finite
      }
    }
    public class BoolBoundedPool : BoundedPool
    {
    }
    public class IntBoundedPool : BoundedPool
    {
      public readonly Expression LowerBound;
      public readonly Expression UpperBound;
      public IntBoundedPool(Expression lowerBound, Expression upperBound) {
        LowerBound = lowerBound;
        UpperBound = upperBound;
      }
      public override bool IsFinite {
        get {
          return LowerBound != null && UpperBound != null;
        }
      }
    }
    public class SetBoundedPool : BoundedPool
    {
      public readonly Expression Set;
      public SetBoundedPool(Expression set) { Set = set; }
    }
    public class SubSetBoundedPool : BoundedPool
    {
      public readonly Expression UpperBound;
      public SubSetBoundedPool(Expression set) { UpperBound = set; }
    }
    public class SuperSetBoundedPool : BoundedPool
    {
      public readonly Expression LowerBound;
      public SuperSetBoundedPool(Expression set) { LowerBound = set; }
    }
    public class MapBoundedPool : BoundedPool
    {
      public readonly Expression Map;
      public MapBoundedPool(Expression map) { Map = map; }
    }
    public class SeqBoundedPool : BoundedPool
    {
      public readonly Expression Seq;
      public SeqBoundedPool(Expression seq) { Seq = seq; }
    }
    public class DatatypeBoundedPool : BoundedPool
    {
      public readonly DatatypeDecl Decl;
      public DatatypeBoundedPool(DatatypeDecl d) { Decl = d; }
    }

    public List<BoundedPool> Bounds;  // initialized and filled in by resolver
    // invariant Bounds == null || Bounds.Count == BoundVars.Count;
    public List<BoundVar> MissingBounds;  // filled in during resolution; remains "null" if bounds can be found
    // invariant Bounds == null || MissingBounds == null;

    public ComprehensionExpr(IToken tok, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
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
        foreach (var e in Attributes.SubExpressions(Attributes)) {
          yield return e;
        }
        if (Range != null) { yield return Range; }
        yield return Term;
      }
    }
  }

  public abstract class QuantifierExpr : ComprehensionExpr, TypeParameter.ParentType {
    public List<TypeParameter> TypeArgs;
    private static int quantCount = 0;
    private readonly int quantUnique;
    public string FullName {
      get {
        return "q$" + quantUnique;
      }
    }
    public String Refresh(String s, ref int counter) {
      return s + "#" + counter++ + FullName; 
    }
    public TypeParameter Refresh(TypeParameter p, ref int counter) {
      var cp = new TypeParameter(p.tok, counter++ + "#" + p.Name, p.EqualitySupport);
      cp.Parent = this;
      return cp;
    }
    [ContractInvariantMethod]
    void ObjectInvariant() {
      var _scratch = true;
      Contract.Invariant(Attributes.ContainsBool(Attributes, "typeQuantifier", ref _scratch) || TypeArgs.Count == 0);
    }
    public QuantifierExpr(IToken tok, List<TypeParameter> tvars, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
      : base(tok, bvars, range, term, attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(term != null);
      this.TypeArgs = tvars;
      this.quantUnique = quantCount++;
    }
    public abstract Expression LogicalBody();
  }

  public class ForallExpr : QuantifierExpr {
    public ForallExpr(IToken tok, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
      : this(tok, new List<TypeParameter>(), bvars, range, term, attrs) {
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(tok != null);
      Contract.Requires(term != null);
    }
    public ForallExpr(IToken tok, List<TypeParameter> tvars, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
      : base(tok, tvars, bvars, range, term, attrs) {
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(tok != null);
      Contract.Requires(term != null);
    }
    public override Expression LogicalBody() {
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
    public ExistsExpr(IToken tok, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
      : this(tok, new List<TypeParameter>(), bvars, range, term, attrs) {
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(tok != null);
      Contract.Requires(term != null);
    }
    public ExistsExpr(IToken tok, List<TypeParameter> tvars, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
      : base(tok, tvars, bvars, range, term, attrs) {
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(tok != null);
      Contract.Requires(term != null);
    }
    public override Expression LogicalBody() {
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

    public SetComprehension(IToken tok, List<BoundVar> bvars, Expression range, Expression term)
      : base(tok, bvars, range, term ?? new IdentifierExpr(tok, bvars[0].Name), null) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(1 <= bvars.Count);
      Contract.Requires(range != null);

      TermIsImplicit = term == null;
    }
  }
  public class MapComprehension : ComprehensionExpr
  {
    public MapComprehension(IToken tok, List<BoundVar> bvars, Expression range, Expression term)
      : base(tok, bvars, range, term, null) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(1 <= bvars.Count);
      Contract.Requires(range != null);
      Contract.Requires(term != null);
    }
  }

  public class LambdaExpr : ComprehensionExpr
  {
    private static int lamUniques = 0;

    public readonly bool OneShot;

    public readonly List<FrameExpression> Reads;

    public string MkName(string nm) {
      return "$l" + lamUniques++ + "#" + nm; 
    }

    public LambdaExpr(IToken tok, bool oneShot, List<BoundVar> bvars, Expression requires, List<FrameExpression> reads, Expression body)
      : base(tok, bvars, requires, body, null) 
    {
      Contract.Requires(reads != null); 
      Reads = reads;
      OneShot = oneShot;
    }

    // Synonym
    public Expression Body {
      get {
        return Term;
      }
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Term;
        if (Range != null) {
          yield return Range;
        }
        foreach (var read in Reads) {
          yield return read.E;
        }
      }
    }

  }


  public class WildcardExpr : Expression
  {  // a WildcardExpr can occur only in reads clauses and a loop's decreases clauses (with different meanings)
    public WildcardExpr(IToken tok)
      : base(tok) {
      Contract.Requires(tok != null);
    }
  }

  /// <summary>
  /// A StmtExpr has the form S;E where S is a statement (from a restricted set) and E is an expression.
  /// The expression S;E evaluates to whatever E evaluates to, but its well-formedness comes down to
  /// executing S (which itself must be well-formed) and then checking the well-formedness of E.
  /// </summary>
  public class StmtExpr : Expression
  {
    public readonly Statement S;
    public readonly Expression E;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(S != null);
      Contract.Invariant(E != null);
    }

    public StmtExpr(IToken tok, Statement stmt, Expression expr)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(stmt != null);
      Contract.Requires(expr != null);
      S = stmt;
      E = expr;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        // Note:  A StmtExpr is unusual in that it contains a statement.  For now, callers
        // of SubExpressions need to be aware of this and handle it specially.
        yield return E;
      }
    }

    /// <summary>
    /// Returns a conclusion that S gives rise to, that is, something that is known after
    /// S is executed.
    /// This method should be called only after successful resolution of the expression.
    /// </summary>
    public Expression GetSConclusion() {
      // this is one place where we actually investigate what kind of statement .S is
      if (S is PredicateStmt) {
        var s = (PredicateStmt)S;
        return s.Expr;
      } else if (S is CalcStmt) {
        var s = (CalcStmt)S;
        return s.Result;
      } else if (S is UpdateStmt) {
        return new LiteralExpr(tok, true);  // one could use the postcondition of the method, suitably instantiated, but "true" is conservative and much simpler :)
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }
    }
  }

  public class ITEExpr : Expression
  {
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
    public readonly List<MatchCaseExpr> Cases;
    public readonly List<DatatypeCtor> MissingCases = new List<DatatypeCtor>();  // filled in during resolution
    public readonly bool UsesOptionalBraces;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Source != null);
      Contract.Invariant(cce.NonNullElements(Cases));
      Contract.Invariant(cce.NonNullElements(MissingCases));
    }

    public MatchExpr(IToken tok, Expression source, [Captured] List<MatchCaseExpr> cases, bool usesOptionalBraces)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(source != null);
      Contract.Requires(cce.NonNullElements(cases));
      this.Source = source;
      this.Cases = cases;
      this.UsesOptionalBraces = usesOptionalBraces;
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

  /// <summary>
  /// A CasePattern is either a BoundVar or a datatype constructor with optional arguments.
  /// Lexically, the CasePattern starts with an identifier.  If it continues with an open paren (as
  /// indicated by Arguments being non-null), then the CasePattern is a datatype constructor.  If
  /// it continues with a colon (which is indicated by Var.Type not being a proxy type), then it is
  /// a BoundVar.  But if it ends with just the identifier, then resolution is required to figure out
  /// which it is; in this case, Var is non-null, because this is the only place where Var.IsGhost
  /// is recorded by the parser.
  /// </summary>
  public class CasePattern
  {
    public readonly IToken tok;
    public readonly string Id;
    // After successful resolution, exactly one of the following two fields is non-null.
    public DatatypeCtor Ctor;  // finalized by resolution (null if the pattern is a bound variable)
    public BoundVar Var;  // finalized by resolution (null if the pattern is a constructor)  Invariant:  Var != null ==> Arguments == null
    public readonly List<CasePattern> Arguments;

    public Expression Expr;  // an r-value version of the CasePattern; filled in by resolution

    public CasePattern(IToken tok, string id, [Captured] List<CasePattern> arguments) {
      Contract.Requires(tok != null);
      Contract.Requires(id != null);
      this.tok = tok;
      Id = id;
      Arguments = arguments;
    }

    public CasePattern(IToken tok, BoundVar bv) {
      Contract.Requires(tok != null);
      Contract.Requires(bv != null);
      this.tok = tok;
      Id = bv.Name;
      Var = bv;
    }

    /// <summary>
    /// Sets the Expr field.  Assumes the CasePattern and its arguments to have been successfully resolved, except for assigning
    /// to Expr.
    /// </summary>
    public void AssembleExpr(List<Type> dtvTypeArgs) {
      Contract.Requires(Var != null || dtvTypeArgs != null);
      if (Var != null) {
        var ie = new IdentifierExpr(this.tok, this.Id);
        ie.Var = this.Var; ie.Type = this.Var.Type;  // resolve here
        this.Expr = ie;
      } else {
        var dtValue = new DatatypeValue(this.tok, this.Ctor.EnclosingDatatype.Name, this.Id, this.Arguments.ConvertAll(arg => arg.Expr));
        dtValue.Ctor = this.Ctor;  // resolve here
        dtValue.InferredTypeArgs.AddRange(dtvTypeArgs);  // resolve here
        dtValue.Type = new UserDefinedType(this.tok, this.Ctor.EnclosingDatatype.Name, this.Ctor.EnclosingDatatype, dtvTypeArgs);
        this.Expr = dtValue;
      }
    }

    public IEnumerable<BoundVar> Vars {
      get {
        if (Var != null) {
          yield return Var;
        } else {
          foreach (var arg in Arguments) {
            foreach (var bv in arg.Vars) {
              yield return bv;
            }
          }
        }
      }
    }
  }

  public abstract class MatchCase
  {
    public readonly IToken tok;
    public readonly string Id;
    public DatatypeCtor Ctor;  // filled in by resolution
    public readonly List<BoundVar> Arguments;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
      Contract.Invariant(Id != null);
      Contract.Invariant(cce.NonNullElements(Arguments));
    }

    public MatchCase(IToken tok, string id, [Captured] List<BoundVar> arguments) {
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
    public readonly Expression Body;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Body != null);
    }

    public MatchCaseExpr(IToken tok, string id, [Captured] List<BoundVar> arguments, Expression body)
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
    public readonly bool IsFree;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
    }

    private Attributes attributes;
    public Attributes Attributes {
      get {
        return attributes;
      }
      set {
        attributes = value;
      }
    }

    public bool HasAttributes() {
      return Attributes != null;
    }

    public MaybeFreeExpression(Expression e)
      : this(e, false, null)
    {
      Contract.Requires(e != null);
    }

    public MaybeFreeExpression(Expression e, bool isFree)
      : this(e, isFree, null)
    {
      Contract.Requires(e != null);
    }

    public MaybeFreeExpression(Expression e, bool isFree, Attributes attrs) {
      Contract.Requires(e != null);
      E = e;
      IsFree = isFree;
      Attributes = attrs;
    }
  }


  public class FrameExpression {
    public readonly IToken tok;
    public readonly Expression E;  // may be a WildcardExpr
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
      Contract.Invariant(!(E is WildcardExpr) || FieldName == null && Field == null);
    }

    public readonly string FieldName;
    public Field Field;  // filled in during resolution (but is null if FieldName is)

    /// <summary>
    /// If a "fieldName" is given, then "tok" denotes its source location.  Otherwise, "tok"
    /// denotes the source location of "e".
    /// </summary>
    public FrameExpression(IToken tok, Expression e, string fieldName) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
      Contract.Requires(!(e is WildcardExpr) || fieldName == null);
      this.tok = tok;
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

  public class TypeExpr : ParensExpression
  {
    public readonly Type T;
    public TypeExpr(IToken tok, Expression e, Type t) 
      : base(tok, e)
    {
      Contract.Requires(t != null);
      T = t;
    }
    
    public static Expression MaybeTypeExpr(Expression e, Type t) {
      if (t == null) {
        return e;
      } else {
        return new TypeExpr(e.tok, e, t);
      }
    }
  }


  /// <summary>
  /// An AutoGeneratedExpression is simply a wrapper around an expression.  This expression tells the generation of hover text (in the Dafny IDE)
  /// that the expression was no supplied directly in the program text and should therefore be ignored.  In other places, an AutoGeneratedExpression
  /// is just a parenthesized expression, which means that it works just the like expression .E that it contains.
  /// (Ironically, AutoGeneratedExpression, which is like the antithesis of concrete syntax, inherits from ConcreteSyntaxExpression, which perhaps
  /// should rather have been called SemanticsNeutralExpressionWrapper.)
  /// </summary>
  public class AutoGeneratedExpression : ParensExpression
  {
    public AutoGeneratedExpression(IToken tok, Expression e)
      : base(tok, e) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
    }

    /// <summary>
    /// This maker method takes a resolved expression "e" and wraps a resolved AutoGeneratedExpression
    /// around it.
    /// </summary>
    public static AutoGeneratedExpression Create(Expression e) {
      Contract.Requires(e != null);
      var a = new AutoGeneratedExpression(e.tok, e);
      a.type = e.Type;
      a.ResolvedExpression = e;
      return a;
    }
  }

  /// <summary>
  /// A NegationExpression e represents the value -e and is syntactic shorthand
  /// for 0-e (for integers) or 0.0-e (for reals).
  /// </summary>
  public class NegationExpression : ConcreteSyntaxExpression
  {
    public readonly Expression E;
    public NegationExpression(IToken tok, Expression e)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
      E = e;
    }
  }

  public class ChainingExpression : ConcreteSyntaxExpression
  {
    public readonly List<Expression> Operands;
    public readonly List<BinaryExpr.Opcode> Operators;
    public readonly List<Expression/*?*/> PrefixLimits;
    public readonly Expression E;
    public ChainingExpression(IToken tok, List<Expression> operands, List<BinaryExpr.Opcode> operators, List<Expression/*?*/> prefixLimits, Expression desugaring)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(operands != null);
      Contract.Requires(operators != null);
      Contract.Requires(desugaring != null);
      Contract.Requires(operands.Count == operators.Count + 1);

      Operands = operands;
      Operators = operators;
      PrefixLimits = prefixLimits;
      E = desugaring;
    }
  }

  /// <summary>
  /// An ExprDotName desugars into either a FieldSelectExpr or a FunctionCallExpr (with a parameterless predicate function).
  /// </summary>
  public class ExprDotName : ConcreteSyntaxExpression
  {
    public readonly Expression Obj;
    public readonly string SuffixName;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Obj != null);
      Contract.Invariant(SuffixName != null);
    }

    public ExprDotName(IToken tok, Expression obj, string suffixName)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(obj != null);
      Contract.Requires(suffixName != null);
      this.Obj = obj;
      this.SuffixName = suffixName;
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


  public class Specification<T> where T : class
  {
    public readonly List<T> Expressions;

    [ContractInvariantMethod]
    private void ObjectInvariant()
    {
      Contract.Invariant(Expressions == null || cce.NonNullElements<T>(Expressions));
    }


    public Specification(List<T> exprs, Attributes attrs)
    {
      Contract.Requires(exprs == null || cce.NonNullElements<T>(exprs));
      Expressions = exprs;
      Attributes = attrs;
    }

    private Attributes attributes;
    public Attributes Attributes
    {
      get
      {
        return attributes;
      }
      set
      {
        attributes = value;
      }
    }

    public bool HasAttributes()
    {
      return Attributes != null;
    }
  }
  public abstract class TranslationTask
  {

  }
  public class MethodCheck : TranslationTask
  {
    public readonly Method Refined;
    public readonly Method Refining;
    public MethodCheck(Method a, Method b) {
      Refined = b;
      Refining = a;
    }
  }
  public class FunctionCheck : TranslationTask
  {
    public readonly Function Refined;
    public readonly Function Refining;
    public FunctionCheck(Function a, Function b) {
      Refined = b;
      Refining = a;
    }
  }

  public class BottomUpVisitor
  {
    public void Visit(Expression expr) {
      Contract.Requires(expr != null);
      // recursively visit all subexpressions and all substatements
      expr.SubExpressions.Iter(Visit);
      if (expr is StmtExpr) {
        // a StmtExpr also has a sub-statement
        var e = (StmtExpr)expr;
        Visit(e.S);
      }
      VisitOneExpr(expr);
    }
    public void Visit(Statement stmt) {
      Contract.Requires(stmt != null);
      // recursively visit all subexpressions and all substatements
      stmt.SubExpressions.Iter(Visit);
      stmt.SubStatements.Iter(Visit);
      VisitOneStmt(stmt);
    }
    protected virtual void VisitOneExpr(Expression expr) {
      Contract.Requires(expr != null);
      // by default, do nothing
    }
    protected virtual void VisitOneStmt(Statement stmt) {
      Contract.Requires(stmt != null);
      // by default, do nothing
    }
  }
  public class TopDownVisitor<State>
  {
    public void Visit(Expression expr, State st) {
      Contract.Requires(expr != null);
      if (VisitOneExpr(expr, ref st)) {
        // recursively visit all subexpressions and all substatements
        expr.SubExpressions.Iter(e => Visit(e, st));
        if (expr is StmtExpr) {
          // a StmtExpr also has a sub-statement
          var e = (StmtExpr)expr;
          Visit(e.S, st);
        }
      }
    }
    public void Visit(Statement stmt, State st) {
      Contract.Requires(stmt != null);
      if (VisitOneStmt(stmt, ref st)) {
        // recursively visit all subexpressions and all substatements
        stmt.SubExpressions.Iter(e => Visit(e, st));
        stmt.SubStatements.Iter(s => Visit(s, st));
      }
    }
    /// <summary>
    /// Visit one expression proper.  This method is invoked before it is invoked on the
    /// sub-parts (sub-expressions and sub-statements).  A return value of "true" says to
    /// continue invoking the method on sub-parts, whereas "false" says not to do so.
    /// The on-return value of "st" is the value that is passed to sub-parts.
    /// </summary>
    protected virtual bool VisitOneExpr(Expression expr, ref State st) {
      Contract.Requires(expr != null);
      return true;  // by default, visit the sub-parts with the same "st"
    }
    /// <summary>
    /// Visit one statement proper.  For the rest of the description of what this method
    /// does, see VisitOneExpr.
    /// </summary>
    protected virtual bool VisitOneStmt(Statement stmt, ref State st) {
      Contract.Requires(stmt != null);
      return true;  // by default, visit the sub-parts with the same "st"
    }
  }
}
