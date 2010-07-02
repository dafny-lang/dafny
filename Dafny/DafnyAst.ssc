//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Text;
using System.Collections.Generic;
using Microsoft.Contracts;
using System.Numerics;
using Microsoft.Boogie;

namespace Microsoft.Dafny
{
  public class Program {
    public readonly string! Name;
    public readonly List<ModuleDecl!>! Modules;
    public Program(string! name, [Captured] List<ModuleDecl!>! modules) {
      Name = name;
      Modules = modules;
    }
  }
  
  public class Attributes {
    public readonly string! Name;
    /*Frozen*/ public readonly List<Argument!>! Args;
    public readonly Attributes Prev;
    
    public Attributes(string! name, [Captured] List<Argument!>! args, Attributes prev)
    {
      Name = name;
      Args = args;
      Prev = prev;
    }
    
    public class Argument {
      public readonly string S;
      public readonly Expression E;
      invariant (S == null) != (E == null);
      
      public Argument(string! s) {
        S = s;
      }
      public Argument(Expression! e) {
        E = e;
      }
    }
  }
  
  // ------------------------------------------------------------------------------------------------------
  
  public abstract class Type {
    public static readonly BoolType! Bool = new BoolType();
    public static readonly IntType! Int = new IntType();
    /// <summary>
    /// Used in error situations in order to reduce further error messages.
    /// </summary>
    [Pure(false)]
    public static Type! Flexible {
      get { return new InferredTypeProxy(); }
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
        UserDefinedType udt = UserDefinedType.DenotesClass(this);
        return udt != null && ((ClassDecl!)udt.ResolvedClass).Name == "array";  // the cast to non-null is guaranteed by postcondition of DenotesClass
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
      get
        ensures result ==> this is UserDefinedType && ((UserDefinedType)this).ResolvedParam != null;
      {
        UserDefinedType ct = this as UserDefinedType;
        return ct != null && ct.ResolvedParam != null;
      }
    }
  }
  
  public abstract class BasicType : Type {
  }
  
  public class BoolType : BasicType {
    [Pure] public override string! ToString() {
      return "bool";
    }
  }
  
  public class IntType : BasicType {
    [Pure] public override string! ToString() {
      return "int";
    }
  }
  
  public class ObjectType : BasicType {
    [Pure] public override string! ToString() {
      return "object";
    }
  }
  
  public abstract class CollectionType : Type {
    public readonly Type! Arg;
    public CollectionType(Type! arg) {
      this.Arg = arg;
    }
  }
  
  public class SetType : CollectionType {
    public SetType(Type! arg) {
      base(arg);
    }
    [Pure] public override string! ToString() {
      assume Arg.IsPeerConsistent;
      return "set<" + Arg + ">";
    }
  }
  
  public class SeqType : CollectionType {
    public SeqType(Type! arg) {
      base(arg);
    }
    [Pure] public override string! ToString() {
      assume Arg.IsPeerConsistent;
      return "seq<" + Arg + ">";
    }
  }
  
  public class UserDefinedType : Type {
    public readonly IToken! tok;
    public readonly string! Name;
    [Rep] public readonly List<Type!>! TypeArgs;
    
    public TopLevelDecl ResolvedClass;  // filled in by resolution, if Name denotes a class/datatype and TypeArgs match the type parameters of that class/datatype
    public TypeParameter ResolvedParam;  // filled in by resolution, if Name denotes an enclosing type parameter and TypeArgs is the empty list

    public static UserDefinedType! ArrayType(IToken! tok, Type! arg) {
      List<Type!> typeArgs = new List<Type!>();
      typeArgs.Add(arg);
      UserDefinedType udt = new UserDefinedType(tok, "array", typeArgs);
      udt.ResolvedClass = arrayTypeDecl;
      return udt;
    }
    static TopLevelDecl! arrayTypeDecl;
    static UserDefinedType() {
      List<TypeParameter!> typeArgs = new List<TypeParameter!>();
      typeArgs.Add(new TypeParameter(Token.NoToken, "arg"));
      ModuleDecl systemModule = new ModuleDecl(Token.NoToken, "_System", new List<string!>(), null);
      arrayTypeDecl = new ClassDecl(Token.NoToken, "array", systemModule, typeArgs, new List<MemberDecl!>(), null);
    }

    
    public UserDefinedType(IToken! tok, string! name, [Captured] List<Type!>! typeArgs) {
      this.tok = tok;
      this.Name = name;
      this.TypeArgs = typeArgs;
    }
    
    /// <summary>
    /// This constructor constructs a resolved class type
    /// </summary>
    public UserDefinedType(IToken! tok, string! name, TopLevelDecl! cd, [Captured] List<Type!>! typeArgs) {
      this.tok = tok;
      this.Name = name;
      this.TypeArgs = typeArgs;
      this.ResolvedClass = cd;
    }
    
    /// <summary>
    /// This constructor constructs a resolved type parameter
    /// </summary>
    public UserDefinedType(IToken! tok, string! name, TypeParameter! tp) {
      this.tok = tok;
      this.Name = name;
      this.TypeArgs = new List<Type!>();
      this.ResolvedParam = tp;
    }
    
    /// <summary>
    /// If type denotes a resolved class type, then return that class type.
    /// Otherwise, return null.
    /// </summary>
    public static UserDefinedType DenotesClass(Type! type)
      ensures result != null ==> result.ResolvedClass is ClassDecl;
    {
      while (true)
        invariant type.IsPeerConsistent;
      {
        TypeProxy pt = type as TypeProxy;
        if (pt != null && pt.T != null) {
          type = pt.T;
          assume type.IsPeerConsistent;
        } else {
          break;
        }
      }
      UserDefinedType ct = type as UserDefinedType;
      if (ct != null && ct.ResolvedClass is ClassDecl) {
        return ct;
      } else {
        return null;
      }
    }
    
    /// <summary>
    /// If type denotes a resolved class type, then return that class type.
    /// Otherwise, return null.
    /// </summary>
    public static Type! ArrayElementType(Type! type)
      requires type.IsArrayType;
    {
      UserDefinedType udt = DenotesClass(type);
      assert udt != null;
      assert udt.TypeArgs.Count == 1;  // holds true of all array types
      return udt.TypeArgs[0];
    }
    
    [Pure] public override string! ToString() {
      string s = Name;
      if (TypeArgs.Count != 0) {
        string sep = "<";
        foreach (Type t in TypeArgs) {
          assume t.IsPeerConsistent;
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
    internal TypeProxy() { }
    
    [Pure] public override string! ToString() {
      assume T == null || T.IsPeerConsistent;
      return T == null ? "?" : T.ToString();
    }
  }
  
  public abstract class UnrestrictedTypeProxy : TypeProxy { }
  
  /// <summary>
  /// This proxy stands for any type.
  /// </summary>  
  public class InferredTypeProxy : UnrestrictedTypeProxy {
  }
  
  /// <summary>
  /// This proxy stands for any type, but it originates from an instantiated type parameter.
  /// </summary>  
  public class ParamTypeProxy : UnrestrictedTypeProxy {
    TypeParameter! orig;
    public ParamTypeProxy(TypeParameter! orig) {
      this.orig = orig;
    }
  }
  
  public abstract class RestrictedTypeProxy : TypeProxy {
    /// <summary>
    /// The OrderID is used to simplify the unification code.  Each restricted type proxy should use its
    /// own OrderID.
    /// </summary>
    public abstract int OrderID { get; }
  }
  
  /// <summary>
  /// This proxy stands for any datatype.
  /// </summary>  
  public class DatatypeProxy : RestrictedTypeProxy {
    public override int OrderID { get { return 0; } }
  }
  
  /// <summary>
  /// This proxy stands for object or any class/array type.
  /// </summary>  
  public class ObjectTypeProxy : RestrictedTypeProxy {
    public override int OrderID { get { return 1; } }
  }
  
  /// <summary>
  /// This proxy stands for object or any class/array type or a set/sequence of object or a class/array type.
  /// </summary>
  public class ObjectsTypeProxy : RestrictedTypeProxy {
    public override int OrderID { get { return 2; } }
  }
  
  /// <summary>
  /// This proxy stands for:
  ///     set(Arg) or seq(Arg)
  /// </summary>
  public class CollectionTypeProxy : RestrictedTypeProxy {
    public readonly Type! Arg;
    public CollectionTypeProxy(Type! arg) {
      Arg = arg;
    }
    public override int OrderID { get { return 3; } }
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
    public override int OrderID { get { return 4; } }
  }
  
  /// <summary>
  /// This proxy stands for:
  ///     seq(Arg) or array(Arg)
  /// </summary>
  public class IndexableTypeProxy : RestrictedTypeProxy {
    public readonly Type! Arg;
    public IndexableTypeProxy(Type! arg) {
      Arg = arg;
    }
    public override int OrderID { get { return 5; } }
  }

  // ------------------------------------------------------------------------------------------------------
  
  public abstract class Declaration {
    public IToken! tok;
    public readonly string! Name;
    public readonly Attributes Attributes;
    
    public Declaration(IToken! tok, string! name, Attributes attributes) {
      this.tok = tok;
      this.Name = name;
      this.Attributes = attributes;
    }
    
    [Pure]
    public override string! ToString() {
      return Name;
    }
  }
  
  public class TypeParameter : Declaration {
    public interface ParentType { }
    [Peer] ParentType parent;
    public ParentType Parent {
      get {
        return parent;
      }
      [param: Captured]
      set
        requires Parent == null;  // set it only once
        requires value != null;
        // BUGBUG:  The following line is a workaround to tell the verifier that 'value' is not of an Immutable type.
        // A proper solution would be to be able to express that in the program (in a specification or attribute) or
        // to be able to declare 'parent' as [PeerOrImmutable].
        requires value is TopLevelDecl || value is Function || value is Method || value is DatatypeCtor;
        modifies parent;
      {
        parent = value;
      }
    }
    public TypeParameter(IToken! tok, string! name) {
      base(tok, name, null);
    }
  }
  
  public class ModuleDecl : Declaration {
    public readonly List<string!>! Imports;
    public readonly List<TopLevelDecl!>! TopLevelDecls = new List<TopLevelDecl!>();  // filled in by the parser; readonly after that
    public readonly Graph<MemberDecl!>! CallGraph = new Graph<MemberDecl!>();  // filled in during resolution
    public int Height;  // height in the topological sorting of modules; filled in during resolution
    public ModuleDecl(IToken! tok, string! name, [Captured] List<string!>! imports, Attributes attributes) {
      Imports = imports;
      base(tok, name, attributes);
    }
    public virtual bool IsDefaultModule {
      get { return false; }
    }
  }
  
  public class DefaultModuleDecl : ModuleDecl {
    public DefaultModuleDecl() {
      base(Token.NoToken, "_default", new List<string!>(), null);
    }
    public override bool IsDefaultModule {
      get { return true; }
    }
  }
    
  public abstract class TopLevelDecl : Declaration, TypeParameter.ParentType {
    public readonly ModuleDecl! Module;
    public readonly List<TypeParameter!>! TypeArgs;
    
    public TopLevelDecl(IToken! tok, string! name, ModuleDecl! module, List<TypeParameter!>! typeArgs, Attributes attributes) {
      Module = module;
      TypeArgs = typeArgs;
      base(tok, name, attributes);
    }
  }

  public class ClassDecl : TopLevelDecl {
    public readonly List<MemberDecl!>! Members;

    public ClassDecl(IToken! tok, string! name, ModuleDecl! module, List<TypeParameter!>! typeArgs, [Captured] List<MemberDecl!>! members, Attributes attributes) {
      Members = members;
      base(tok, name, module, typeArgs, attributes);
    }
    public virtual bool IsDefaultClass {
      get { return false; }
    }
  }
  
  public class ClassRefinementDecl : ClassDecl {
    public readonly IToken! RefinedClass;
    public ClassDecl Refined; // filled in during resolution 
    public ClassRefinementDecl(IToken! tok, string! name, ModuleDecl! module, List<TypeParameter!>! typeArgs, [Captured] List<MemberDecl!>! members, Attributes attributes, IToken! refinedClass) {
      RefinedClass = refinedClass;
      base(tok, name, module, typeArgs, members, attributes);
    }
  }
  
  public class DefaultClassDecl : ClassDecl {
    public DefaultClassDecl(DefaultModuleDecl! module, [Captured] List<MemberDecl!>! members) {
      base(Token.NoToken, "_default", module, new List<TypeParameter!>(), members, null);
    }
    public override bool IsDefaultClass {
      get { return true; }
    }
  }
  
  public class DatatypeDecl : TopLevelDecl {
    public readonly List<DatatypeCtor!>! Ctors;
    public DatatypeCtor DefaultCtor;  // set during resolution
    
    public DatatypeDecl(IToken! tok, string! name, ModuleDecl! module, List<TypeParameter!>! typeArgs, [Captured] List<DatatypeCtor!>! ctors, Attributes attributes) {
      Ctors = ctors;
      base(tok, name, module, typeArgs, attributes);
    }
  }
  
  public class DatatypeCtor : Declaration, TypeParameter.ParentType {
    public readonly List<TypeParameter!>! TypeArgs;
    public readonly List<Formal!>! Formals;
    // Todo: One could imagine having a precondition on datatype constructors
    public DatatypeDecl EnclosingDatatype;  // filled in during resolution
    
    public DatatypeCtor(IToken! tok, string! name, [Captured] List<TypeParameter!>! typeArgs, [Captured] List<Formal!>! formals,
                        Attributes attributes) {
      this.TypeArgs = typeArgs;
      this.Formals = formals;
      base(tok, name, attributes);
    }
    
    public string! FullName {
      get
        requires EnclosingDatatype != null;
      {
        return "#" + EnclosingDatatype.Name + "." + Name;
      }
    }
  }
  
  public abstract class MemberDecl : Declaration {
    public ClassDecl EnclosingClass;  // filled in during resolution
    
    public MemberDecl(IToken! tok, string! name, Attributes attributes) {
      base(tok, name, attributes);
    }
    /// <summary>
    /// Returns className+"."+memberName.  Available only after resolution.
    /// </summary>
    public string! FullName {
      get
        requires EnclosingClass != null;
      {
        return EnclosingClass.Name + "." + Name;
      }
    }
  }
  
  public class Field : MemberDecl {
    public readonly bool IsGhost;
    public readonly Type! Type;
    
    public Field(IToken! tok, string! name, bool isGhost, Type! type, Attributes attributes) {
      IsGhost = isGhost;
      Type = type;
      base(tok, name, attributes);
    }
  }
  
  public class CouplingInvariant : MemberDecl {
    public readonly Expression! Expr;    
    public readonly List<IToken!>! Toks;
    public List<Formal!> Formals; // filled in during resolution
    public List<Field!> Refined; // filled in during resolution
    
    public CouplingInvariant(List<IToken!>! toks, Expression! expr, Attributes attributes) 
      requires toks.Count > 0;
    {
      Expr = expr;      
      Toks = toks;
      StringBuilder sb = new StringBuilder();
      foreach (IToken tok in toks) 
        sb.Append("_").Append(tok.val);
        
      base(toks[0], "_coupling_invariant" + sb.ToString(), attributes);
    }
    
    public string[] Tokens() {
      string[] result = new string[Toks.Count];
      for (int i = 0; i < Toks.Count; i++)
        result[i] = Toks[i].val;
      return result;
    }      
  }
  
  public interface IVariable {
    string! Name { get; }
    string! UniqueName { get; }
    Type! Type { get; }
    bool IsMutable { get; }
    bool IsGhost { get; }
  }
  
  public abstract class NonglobalVariable : IVariable {
    public readonly IToken! tok;
    readonly string! name;
    public string! Name { get { return name; } }
    readonly int varId = varIdCount++;
    public string! UniqueName { get { return name + "#" + varId; } }
    Type! type;
    [Pure(false)]  // TODO: if Type gets the status of [Frozen], then this attribute is not needed
    public Type! Type { get {
      assume type.IsPeerConsistent;
      while (true)
        invariant type.IsPeerConsistent;
      {
        TypeProxy t = type as TypeProxy;
        if (t != null && t.T != null) {
          type = t.T;
          assume type.IsPeerConsistent;
        } else {
          return type;
        }
      }
    } }
    public abstract bool IsMutable { get; }
    bool isGhost;  // readonly, except for BoundVar's of match expressions/statements during resolution
    public bool IsGhost {
      get { return isGhost; }
      set { isGhost = value; }
    }
    
    public NonglobalVariable(IToken! tok, string! name, Type! type, bool isGhost) {
      this.tok = tok;
      this.name = name;
      this.type = type;
      this.isGhost = isGhost;
    }
    
    internal static int varIdCount;  // this varIdCount is used for both NonglobalVariable's and VarDecl's.
  }
  
  public class Formal : NonglobalVariable {
    public readonly bool InParam;  // true to in-parameter, false for out-parameter
    public override bool IsMutable { get { return !InParam; } }
    
    public Formal(IToken! tok, string! name, Type! type, bool inParam, bool isGhost) {
      InParam = inParam;
      base(tok, name, type, isGhost);
    }
  }
  
  public class BoundVar : NonglobalVariable {
    public override bool IsMutable { get { return false; } }
    
    public BoundVar(IToken! tok, string! name, Type! type) {
      base(tok, name, type, false);
    }
  }
  
  public class Function : MemberDecl, TypeParameter.ParentType {
    public readonly bool IsStatic;
    public readonly bool IsGhost;  // functions are "ghost" by default; a non-ghost function is called a "function method"
    public readonly bool IsUnlimited;
    public bool IsRecursive;  // filled in during resolution
    public readonly List<TypeParameter!>! TypeArgs;
    public readonly List<Formal!>! Formals;
    public readonly Type! ResultType;
    public readonly List<Expression!>! Req;
    public readonly List<FrameExpression!>! Reads;
    public readonly List<Expression!>! Decreases;
    public readonly Expression Body;  // an extended expression
    
    public Function(IToken! tok, string! name, bool isStatic, bool isGhost, bool isUnlimited, [Captured] List<TypeParameter!>! typeArgs, [Captured] List<Formal!>! formals, Type! resultType,
                    List<Expression!>! req, List<FrameExpression!>! reads, List<Expression!>! decreases, Expression body, Attributes attributes) {
      this.IsStatic = isStatic;
      this.IsGhost = isGhost;
      this.IsUnlimited = isUnlimited;
      this.TypeArgs = typeArgs;
      this.Formals = formals;
      this.ResultType = resultType;
      this.Req = req;
      this.Reads = reads;
      this.Decreases = decreases;
      this.Body = body;
      base(tok, name, attributes);
    }
  }
  
  public class Method : MemberDecl, TypeParameter.ParentType {
    public readonly bool IsStatic;
    public readonly bool IsGhost;
    public readonly List<TypeParameter!>! TypeArgs;
    public readonly List<Formal!>! Ins;
    public readonly List<Formal!>! Outs;
    public readonly List<MaybeFreeExpression!>! Req;
    public readonly List<FrameExpression!>! Mod;
    public readonly List<MaybeFreeExpression!>! Ens;
    public readonly List<Expression!>! Decreases;
    public readonly BlockStmt Body;
    
    public Method(IToken! tok, string! name,
                  bool isStatic, bool isGhost,
                  [Captured] List<TypeParameter!>! typeArgs,
                  [Captured] List<Formal!>! ins, [Captured] List<Formal!>! outs,
                  [Captured] List<MaybeFreeExpression!>! req, [Captured] List<FrameExpression!>! mod, [Captured] List<MaybeFreeExpression!>! ens,
                  [Captured] List<Expression!>! decreases,
                  [Captured] BlockStmt body,
                  Attributes attributes) {
      this.IsStatic = isStatic;
      this.IsGhost = isGhost;
      this.TypeArgs = typeArgs;
      this.Ins = ins;
      this.Outs = outs;
      this.Req = req;
      this.Mod = mod;
      this.Ens = ens;
      this.Decreases = decreases;
      this.Body = body;
      base(tok, name, attributes);
    }
  }

  public class MethodRefinement : Method {    
    public Method Refined; // filled in during resolution
    public MethodRefinement(IToken! tok, string! name,
                  bool isStatic, bool isGhost,
                  [Captured] List<TypeParameter!>! typeArgs,
                  [Captured] List<Formal!>! ins, [Captured] List<Formal!>! outs,
                  [Captured] List<MaybeFreeExpression!>! req, [Captured] List<FrameExpression!>! mod, [Captured] List<MaybeFreeExpression!>! ens,
                  [Captured] List<Expression!>! decreases,
                  [Captured] BlockStmt body,
                  Attributes attributes) {
      base(tok, name, isStatic, isGhost, typeArgs, ins, outs, req, mod, ens, decreases, body, attributes);  
    }
  }
  
  // ------------------------------------------------------------------------------------------------------
  
  public abstract class Statement {
    public readonly IToken! Tok;
    public bool IsGhost;  // filled in by resolution
    public Statement(IToken! tok) {
      this.Tok = tok;
    }
  }
  
  public abstract class PredicateStmt : Statement {
    [Peer] public readonly Expression! Expr;
    [Captured]
    public PredicateStmt(IToken! tok, Expression! expr)
      ensures Owner.Same(this, expr);
    {
      base(tok);
      Owner.AssignSame(this, expr);
      this.Expr = expr;
    }
  }
  
  public class AssertStmt : PredicateStmt {
    [Captured]
    public AssertStmt(IToken! tok, Expression! expr)
      ensures Owner.Same(this, expr);
    {
      base(tok, expr);
    }
  }
  
  public class AssumeStmt : PredicateStmt {
    [Captured]
    public AssumeStmt(IToken! tok, Expression! expr)
      ensures Owner.Same(this, expr);
    {
      base(tok, expr);
    }
  }
  
  public class UseStmt : PredicateStmt {
    [Captured]
    public UseStmt(IToken! tok, Expression! expr)
      ensures Owner.Same(this, expr);
    {
      base(tok, expr);
    }
    [Peer] private FunctionCallExpr fce;
    /// <summary>
    /// This method assumes the statement has been successfully resolved.
    /// </summary>
    [Pure(false)]
    public FunctionCallExpr! FunctionCallExpr {
      get {
        if (fce == null) {
          Expression expr = Expr;
          while (true)
            invariant Owner.Same(this, expr);
          {
            if (expr is OldExpr) {
              expr = ((OldExpr)expr).E;
            } else {
              break;
            }
          }
          assume expr is FunctionCallExpr;
          fce = (FunctionCallExpr)expr;
        }
        return fce;
      }
    }
    public bool EvalInOld {
      get {
        return Expr is OldExpr;
      }
    }
  }
  
  public class PrintStmt : Statement {
    public readonly List<Attributes.Argument!>! Args;
    public PrintStmt(IToken! tok, List<Attributes.Argument!>! args)
    {
      base(tok);
      Args = args;
    }
  }
  
  public class LabelStmt : Statement {
    public readonly string! Label;
    public LabelStmt(IToken! tok, string! label) {
      this.Label = label;
      base(tok);
    }
  }
  
  public class BreakStmt : Statement {
    public readonly string TargetLabel;
    public Statement TargetStmt;  // filled in during resolution
    
    public BreakStmt(IToken! tok, string targetLabel) {
      this.TargetLabel = targetLabel;
      base(tok);
    }
  }
  
  public class ReturnStmt : Statement {
    public ReturnStmt(IToken! tok) {
      base(tok);
    }
  }
  
  public abstract class AssignmentRhs {
    internal AssignmentRhs() { }
  }
  
  public abstract class DeterminedAssignmentRhs : AssignmentRhs {
    internal DeterminedAssignmentRhs() { }
  }
  
  public class ExprRhs : DeterminedAssignmentRhs {
    public readonly Expression! Expr;
    public ExprRhs(Expression! expr) {
      Expr = expr;
    }
  }
  
  public class TypeRhs : DeterminedAssignmentRhs {
    public readonly Type! EType;
    public readonly Expression ArraySize;
    public TypeRhs(Type! type) {
      EType = type;
    }
    public TypeRhs(Type! type, Expression! arraySize) {
      EType = type;
      ArraySize = arraySize;
    }
  }
  
  public class HavocRhs : AssignmentRhs {
  }

  public class AssignStmt : Statement {
    public readonly Expression! Lhs;
    public readonly AssignmentRhs! Rhs;
    public AssignStmt(IToken! tok, Expression! lhs, Expression! rhs) {  // ordinary assignment statement
      this.Lhs = lhs;
      this.Rhs = new ExprRhs(rhs);
      base(tok);
    }
    public AssignStmt(IToken! tok, Expression! lhs, Type! type) {  // alloc statement
      this.Lhs = lhs;
      this.Rhs = new TypeRhs(type);
      base(tok);
    }
    public AssignStmt(IToken! tok, Expression! lhs, Type! type, Expression! arraySize) {  // array alloc statement
      this.Lhs = lhs;
      this.Rhs = new TypeRhs(type, arraySize);
      base(tok);
    }
    public AssignStmt(IToken! tok, Expression! lhs) {  // havoc
      this.Lhs = lhs;
      this.Rhs = new HavocRhs();
      base(tok);
    }
  }
  
  public class VarDecl : Statement, IVariable {
    readonly string! name;
    public string! Name { get { return name; } }
    readonly int varId = NonglobalVariable.varIdCount++;
    public string! UniqueName { get { return name + "#" + varId; } }
    public readonly Type OptionalType;  // this is the type mentioned in the declaration, if any
    internal Type type;  // this is the declared or inferred type of the variable; it is non-null after resolution (even if resolution fails)
    [Pure(false)]
    public Type! Type { get {
      assume type != null;  /* we assume object has been resolved */
      assume type.IsPeerConsistent;
      while (true)
        invariant type != null && type.IsPeerConsistent;
      {
        TypeProxy t = type as TypeProxy;
        if (t != null && t.T != null) {
          type = t.T;
          assume type.IsPeerConsistent;
        } else {
          return type;
        }
      }
    } }
    public bool IsMutable { get { return true; } }
    bool IVariable.IsGhost { get { return base.IsGhost; } }

    public readonly DeterminedAssignmentRhs Rhs;
    invariant OptionalType != null || Rhs != null;
    
    public VarDecl(IToken! tok, string! name, Type type, bool isGhost, DeterminedAssignmentRhs rhs)
      requires type != null || rhs != null;
    {
      this.name = name;
      this.OptionalType = type;
      this.IsGhost = isGhost;
      this.Rhs = rhs;
      base(tok);
    }
  }
  
  public class AutoVarDecl : VarDecl {
    public readonly int Index;
    public AutoVarDecl(IToken! tok, string! name, Type! type, int index)
    {
      Index = index;
      base(tok, name, type, false, null);
    }
    /// <summary>
    /// This method retrospectively makes the VarDecl a ghost.  It is to be used only during resolution.
    /// </summary>
    public void MakeGhost() {
      base.IsGhost = true;
    }
  }
  
  public class CallStmt : Statement {
    public readonly List<AutoVarDecl!>! NewVars;
    public readonly List<IdentifierExpr!>! Lhs;
    public readonly Expression! Receiver;
    public readonly string! MethodName;
    public readonly List<Expression!>! Args;
    public Method Method;  // filled in by resolution
    
    public CallStmt(IToken! tok, List<AutoVarDecl!>! newVars, List<IdentifierExpr!>! lhs, Expression! receiver, string! methodName, List<Expression!>! args) {
      this.NewVars = newVars;
      this.Lhs = lhs;
      this.Receiver = receiver;
      this.MethodName = methodName;
      this.Args = args;
      base(tok);
    }
  }
  
  public class BlockStmt : Statement {
    public readonly List<Statement!>! Body;
    public BlockStmt(IToken! tok, [Captured] List<Statement!>! body) {
      this.Body = body;
      base(tok);
    }
  }
  
  public class IfStmt : Statement {
    public readonly Expression Guard;
    public readonly Statement! Thn;
    public readonly Statement Els;
    invariant Els == null || Els is BlockStmt || Els is IfStmt;
    
    public IfStmt(IToken! tok, Expression guard, Statement! thn, Statement els)
      requires els == null || els is BlockStmt || els is IfStmt;
    {
      this.Guard = guard;
      this.Thn = thn;
      this.Els = els;
      base(tok);
    }
  }

  public class WhileStmt : Statement {
    public readonly Expression Guard;
    public readonly List<MaybeFreeExpression!>! Invariants;
    public readonly List<Expression!>! Decreases;
    public readonly Statement! Body;
    
    public WhileStmt(IToken! tok, Expression guard,
                     List<MaybeFreeExpression!>! invariants, List<Expression!>! decreases,
                     Statement! body) {
      this.Guard = guard;
      this.Invariants = invariants;
      this.Decreases = decreases;
      this.Body = body;
      base(tok);
    }
  }
  
  public class ForeachStmt : Statement {
    public readonly BoundVar! BoundVar;
    public readonly Expression! Collection;
    public readonly Expression! Range;
    public readonly List<PredicateStmt!>! BodyPrefix;
    public readonly AssignStmt! BodyAssign;
    
    public ForeachStmt(IToken! tok, BoundVar! boundVar, Expression! collection, Expression! range, List<PredicateStmt!>! bodyPrefix, AssignStmt! bodyAssign) {
      this.BoundVar = boundVar;
      this.Collection = collection;
      this.Range = range;
      this.BodyPrefix = bodyPrefix;
      this.BodyAssign = bodyAssign;
      base(tok);
    }
  }
  
  class MatchStmt : Statement {
    public readonly Expression! Source;
    public readonly List<MatchCaseStmt!>! Cases;
    
    public MatchStmt(IToken! tok, Expression! source, [Captured] List<MatchCaseStmt!>! cases) {
      this.Source = source;
      this.Cases = cases;
      base(tok);
    }
  }
  
  public class MatchCaseStmt {
    public readonly IToken! tok;
    public readonly string! Id;
    public DatatypeCtor Ctor;  // filled in by resolution
    public readonly List<BoundVar!>! Arguments;
    public readonly List<Statement!>! Body;
    
    public MatchCaseStmt(IToken! tok, string! id, [Captured] List<BoundVar!>! arguments, [Captured] List<Statement!>! body) {
      this.tok = tok;
      this.Id = id;
      this.Arguments = arguments;
      this.Body = body;
    }
  }
  
  // ------------------------------------------------------------------------------------------------------
  
  public abstract class Expression {
    public readonly IToken! tok;
    protected Type type;
    public Type Type {  // filled in during resolution
      [Verify(false)]  // TODO: how do we allow Type.get to modify type and still be [Pure]?
      [Additive]  // validity of proper subclasses is not required
      get
        ensures type == null ==> result == null;  // useful in conjunction with postcondition of constructor
      {
        while (true) {
          TypeProxy t = type as TypeProxy;
          if (t != null && t.T != null) {
            type = t.T;
          } else {
            assume type == null || type.IsPeerConsistent;
            return type;
          }
        }
      }
      [NoDefaultContract]  // no particular validity of 'this' is required, except that it not be committed
      set
        requires this.IsValid;
        requires Type == null;  // set it only once
        requires value != null && value.IsPeerConsistent;
        modifies type;
      {
        type = value;
        while (true) {
          TypeProxy t = type as TypeProxy;
          if (t != null && t.T != null) {
            type = t.T;
          } else {
            return;
          }
        }
      }
    }
    
    public Expression(IToken! tok)
      ensures type == null;  // we would have liked to have written Type==null, but that's not admissible or provable
    {
      this.tok = tok;
    }
  }
  
  public class LiteralExpr : Expression {
    public readonly object Value;
    
    public static bool IsTrue(Expression! e) {
      if (e is LiteralExpr) {
        LiteralExpr le = (LiteralExpr)e;
        return le.Value is bool && (bool)le.Value;
      } else {
        return false;
      }
    }
    
    public LiteralExpr(IToken! tok) {  // represents the Dafny literal "null"
      this.Value = null;
      base(tok);
    }
    
    public LiteralExpr(IToken! tok, BigInteger n)
      requires 0 <= n.Sign;
    {
      this.Value = n;
      base(tok);
    }
    
    public LiteralExpr(IToken! tok, int n)
      requires 0 <= n;
    {
      this(tok, new BigInteger(n));
    }
    
    public LiteralExpr(IToken! tok, bool b) {
      this.Value = b;
      base(tok);
    }
  }
  
  public class DatatypeValue : Expression {
    public readonly string! DatatypeName;
    public readonly string! MemberName;
    public readonly List<Expression!>! Arguments;
    public DatatypeCtor Ctor;  // filled in by resolution
    public List<Type!>! InferredTypeArgs = new List<Type!>();  // filled in by resolution
    
    public DatatypeValue(IToken! tok, string! datatypeName, string! memberName, [Captured] List<Expression!>! arguments) {
      this.DatatypeName = datatypeName;
      this.MemberName = memberName;
      this.Arguments = arguments;
      base(tok);
    }
  }
  
  public class ThisExpr : Expression {
    public ThisExpr(IToken! tok) {
      base(tok);
    }
  }
  
  public class ImplicitThisExpr : ThisExpr {
    public ImplicitThisExpr(IToken! tok) {
      base(tok);
    }
  }
  
  public class IdentifierExpr : Expression {
    public readonly string! Name;
    public IVariable Var;  // filled in by resolution

    public IdentifierExpr(IToken! tok, string! name) {
      Name = name;
      base(tok);
    }
  }

  public abstract class DisplayExpression : Expression {
    public readonly List<Expression!>! Elements;
    public DisplayExpression(IToken! tok, List<Expression!>! elements) {
      Elements = elements;
      base(tok);
    }
  }
    
  public class SetDisplayExpr : DisplayExpression {
    public SetDisplayExpr(IToken! tok, List<Expression!>! elements) {
      base(tok, elements);
    }
  }
    
  public class SeqDisplayExpr : DisplayExpression {
    public SeqDisplayExpr(IToken! tok, List<Expression!>! elements) {
      base(tok, elements);
    }
  }
    
  public class FieldSelectExpr : Expression {
    public readonly Expression! Obj;
    public readonly string! FieldName;
    public Field Field;  // filled in by resolution
    
    public FieldSelectExpr(IToken! tok, Expression! obj, string! fieldName) {
      this.Obj = obj;
      this.FieldName = fieldName;
      base(tok);
    }
  }
  
  public class SeqSelectExpr : Expression {
    public readonly bool SelectOne;  // false means select a range
    public readonly Expression! Seq;
    public readonly Expression E0;
    public readonly Expression E1;
    invariant SelectOne ==> E1 == null;
    invariant E0 != null || E1 != null;
    
    public SeqSelectExpr(IToken! tok, bool selectOne, Expression! seq, Expression e0, Expression e1)
      requires selectOne ==> e1 == null;
      requires e0 != null || e1 != null;
    {
      SelectOne = selectOne;
      Seq = seq;
      E0 = e0;
      E1 = e1;
      base(tok);
    }
  }

  public class SeqUpdateExpr : Expression {
    public readonly Expression! Seq;
    public readonly Expression! Index;
    public readonly Expression! Value;
    
    public SeqUpdateExpr(IToken! tok, Expression! seq, Expression! index, Expression! val)
    {
      Seq = seq;
      Index = index;
      Value = val;
      base(tok);
    }
  }

  public class FunctionCallExpr : Expression {
    public readonly string! Name;
    [Peer] public readonly Expression! Receiver;
    [Peer] public readonly List<Expression!>! Args;
    public Function Function;  // filled in by resolution
    
    [Captured]
    public FunctionCallExpr(IToken! tok, string! fn, Expression! receiver, [Captured] List<Expression!>! args)
      ensures type == null;
      ensures Owner.Same(this, receiver);
    {
      base(tok);
      this.Name = fn;
      Owner.AssignSame(this, receiver);
      this.Receiver = receiver;
      this.Args = args;
    }
  }
  
  public class OldExpr : Expression {
    [Peer] public readonly Expression! E;
    [Captured]
    public OldExpr(IToken! tok, Expression! expr) {
      base(tok);
      Owner.AssignSame(this, expr);
      E = expr;
    }
  }

  public class FreshExpr : Expression {
    public readonly Expression! E;
    public FreshExpr(IToken! tok, Expression! expr) {
      E = expr;
      base(tok);
    }
  }
  
  public class UnaryExpr : Expression {
    public enum Opcode { Not, SeqLength }
    public readonly Opcode Op;
    public readonly Expression! E;
    
    public UnaryExpr(IToken! tok, Opcode op, Expression! e) {
      this.Op = op;
      this.E = e;
      base(tok);
    }
  }
  
  public class BinaryExpr : Expression {
    public enum Opcode { Iff, Imp, And, Or,
                         Eq, Neq, Lt, Le, Ge, Gt,
                         Disjoint, In, NotIn,
                         Add, Sub, Mul, Div, Mod }
    public readonly Opcode Op;
    public enum ResolvedOpcode {
      // logical operators
      Iff, Imp, And, Or,
      // non-collection types
      EqCommon, NeqCommon,
      // integers
      Lt, Le, Ge, Gt, Add, Sub, Mul, Div, Mod,
      // sets
      SetEq, SetNeq, ProperSubset, Subset, Superset, ProperSuperset, Disjoint, InSet, NotInSet,
      Union, Intersection, SetDifference,
      // sequences
      SeqEq, SeqNeq, ProperPrefix, Prefix, Concat, InSeq, NotInSeq,
      // datatypes
      RankLt, RankGt
    }
    public ResolvedOpcode ResolvedOp;  // filled in by resolution
                                 
    public static string! OpcodeString(Opcode op) {
      switch (op) {
        case Opcode.Iff:  return "<==>";
        case Opcode.Imp:  return "==>";
        case Opcode.And:  return "&&";
        case Opcode.Or:  return "||";
        case Opcode.Eq:  return "==";
        case Opcode.Lt:  return "<";
        case Opcode.Gt:  return ">";
        case Opcode.Le:  return "<=";
        case Opcode.Ge:  return ">=";
        case Opcode.Neq:  return "!=";
        case Opcode.Disjoint:  return "!!";
        case Opcode.In:  return "in";
        case Opcode.NotIn:  return "!in";
        case Opcode.Add:  return "+";
        case Opcode.Sub:  return "-";
        case Opcode.Mul:  return "*";
        case Opcode.Div:  return "/";
        case Opcode.Mod:  return "%";
        default:
          assert false;  // unexpected operator
      }
    }
    public readonly Expression! E0;
    public readonly Expression! E1;
    
    public BinaryExpr(IToken! tok, Opcode op, Expression! e0, Expression! e1) {
      this.Op = op;
      this.E0 = e0;
      this.E1 = e1;
      base(tok);
    }
  }
  
  public abstract class QuantifierExpr : Expression {
    public readonly List<BoundVar!>! BoundVars;
    public readonly Expression! Body;
    public readonly Triggers Trigs;
    public readonly Attributes Attributes;
    
    public QuantifierExpr(IToken! tok, List<BoundVar!>! bvars, Expression! body, Triggers trigs, Attributes attrs) {
      this.BoundVars = bvars;
      this.Body = body;
      this.Trigs = trigs;
      this.Attributes = attrs;
      base(tok);
    }
  }
  
  public class Triggers {
    public readonly List<Expression!>! Terms;
    public readonly Triggers Prev;
    
    public Triggers(List<Expression!>! terms, Triggers prev) {
      this.Terms = terms;
      this.Prev = prev;
    }
  }
  
  public class ForallExpr : QuantifierExpr {
    public ForallExpr(IToken! tok, List<BoundVar!>! bvars, Expression! body, Triggers trig, Attributes attrs) {
      base(tok, bvars, body, trig, attrs);
    }
  }
  
  public class ExistsExpr : QuantifierExpr {
    public ExistsExpr(IToken! tok, List<BoundVar!>! bvars, Expression! body, Triggers trig, Attributes attrs) {
      base(tok, bvars, body, trig, attrs);
    }
  }
  
  public class WildcardExpr : Expression {  // a WildcardExpr can occur only in reads clauses and a loop's decreases clauses (with different meanings)
    public WildcardExpr(IToken! tok) {
      base(tok);
    }
  }
  
  public class ITEExpr : Expression {
    public readonly Expression! Test;
    public readonly Expression! Thn;
    public readonly Expression! Els;
    
    public ITEExpr(IToken! tok, Expression! test, Expression! thn, Expression! els) {
      this.Test = test;
      this.Thn = thn;
      this.Els = els;
      base(tok);
    }
  }
  
  public class MatchExpr : Expression {  // a MatchExpr is an "extended expression" and is only allowed in certain places
    public readonly Expression! Source;
    public readonly List<MatchCaseExpr!>! Cases;
    
    public MatchExpr(IToken! tok, Expression! source, [Captured] List<MatchCaseExpr!>! cases) {
      this.Source = source;
      this.Cases = cases;
      base(tok);
    }
  }
  
  public class MatchCaseExpr {
    public readonly IToken! tok;
    public readonly string! Id;
    public DatatypeCtor Ctor;  // filled in by resolution
    public readonly List<BoundVar!>! Arguments;
    public readonly Expression! Body;
    
    public MatchCaseExpr(IToken! tok, string! id, [Captured] List<BoundVar!>! arguments, Expression! body) {
      this.tok = tok;
      this.Id = id;
      this.Arguments = arguments;
      this.Body = body;
    }
  }
  
  public class BoxingCastExpr : Expression {  // a BoxingCastExpr is used only as a temporary placeholding during translation
    public readonly Expression! E;
    public readonly Type! FromType;
    public readonly Type! ToType;
    
    public BoxingCastExpr(Expression! e, Type! fromType, Type! toType) {
      base(e.tok);
      E = e;
      FromType = fromType;
      ToType = toType;
    }
  }
  
  public class UnboxingCastExpr : Expression {  // an UnboxingCastExpr is used only as a temporary placeholding during translation
    public readonly Expression! E;
    public readonly Type! FromType;
    public readonly Type! ToType;
    
    public UnboxingCastExpr(Expression! e, Type! fromType, Type! toType) {
      base(e.tok);
      E = e;
      FromType = fromType;
      ToType = toType;
    }
  }
  
  public class MaybeFreeExpression {
    public readonly Expression! E;
    public readonly bool IsFree;
    public MaybeFreeExpression(Expression! e, bool isFree) {
      E = e;
      IsFree = isFree;
    }
  }
  
  public class FrameExpression {
    public readonly Expression! E;  // may be a WildcardExpr
    public readonly string FieldName;
    public Field Field;  // filled in during resolution (but is null if FieldName is)
    invariant E is WildcardExpr ==> FieldName == null && Field == null;

    public FrameExpression(Expression! e, string fieldName)
      requires e is WildcardExpr ==> fieldName == null;
    {
      E = e;
      FieldName = fieldName;
    }
  }
}
