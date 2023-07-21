using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// An ICodeContext is an ICallable or a NoContext.
/// </summary>
public interface ICodeContext : IASTVisitorContext {
  bool IsGhost { get; }
  List<TypeParameter> TypeArgs { get; }
  List<Formal> Ins { get; }
  bool MustReverify { get; }
  string FullSanitizedName { get; }
  bool AllowsNontermination { get; }
}


/// <summary>
/// Some declarations have more than one context. For example, a subset type has a constraint
/// (which is a ghost context) and a witness (which may be a compiled context). To distinguish
/// between these two, the declaration is wrapped inside a CodeContextWrapper.
/// </summary>
public class CodeContextWrapper : ICodeContext {
  protected readonly ICodeContext inner;
  private readonly bool isGhostContext;
  public CodeContextWrapper(ICodeContext inner, bool isGhostContext) {
    this.inner = inner;
    this.isGhostContext = isGhostContext;
  }

  public bool IsGhost => isGhostContext;
  public List<TypeParameter> TypeArgs => inner.TypeArgs;
  public List<Formal> Ins => inner.Ins;
  public ModuleDefinition EnclosingModule => inner.EnclosingModule;
  public bool MustReverify => inner.MustReverify;
  public string FullSanitizedName => inner.FullSanitizedName;
  public bool AllowsNontermination => inner.AllowsNontermination;

  public static ICodeContext Unwrap(ICodeContext codeContext) {
    while (codeContext is CodeContextWrapper ccw) {
      codeContext = ccw.inner;
    }
    return codeContext;
  }
}


/// <summary>
/// An ICallable is a Function, Method, IteratorDecl, or (less fitting for the name ICallable) RedirectingTypeDecl or DatatypeDecl.
/// </summary>
public interface ICallable : ICodeContext, INode {
  string WhatKind { get; }
  string NameRelativeToModule { get; }
  Specification<Expression> Decreases { get; }
  /// <summary>
  /// The InferredDecreases property says whether or not a process was attempted to provide a default decreases
  /// clause.  If such a process was attempted, even if the resulting decreases clause turned out to be empty,
  /// the property will get the value "true".  This is so that a useful error message can be provided.
  /// </summary>
  bool InferredDecreases { get; set; }
  bool AllowsAllocation { get; }
}


/// <summary>
/// This class allows an ICallable to be treated as ghost/compiled according to the "isGhostContext"
/// parameter.
///
/// This class is to ICallable what CodeContextWrapper is to ICodeContext.
/// </summary>
public class CallableWrapper : CodeContextWrapper, ICallable {
  public CallableWrapper(ICallable callable, bool isGhostContext)
    : base(callable, isGhostContext) {
  }

  protected ICallable cwInner => (ICallable)inner;
  public IToken Tok => cwInner.Tok;
  public IEnumerable<Node> Children => cwInner.Children;

  public string WhatKind => cwInner.WhatKind;
  public string NameRelativeToModule => cwInner.NameRelativeToModule;
  public Specification<Expression> Decreases => cwInner.Decreases;

  public bool InferredDecreases {
    get => cwInner.InferredDecreases;
    set { cwInner.InferredDecreases = value; }
  }

  public bool AllowsAllocation => cwInner.AllowsAllocation;
  public RangeToken RangeToken => cwInner.RangeToken;
}


public class DontUseICallable : ICallable {
  public string WhatKind { get { throw new cce.UnreachableException(); } }
  public bool IsGhost { get { throw new cce.UnreachableException(); } }
  public List<TypeParameter> TypeArgs { get { throw new cce.UnreachableException(); } }
  public List<Formal> Ins { get { throw new cce.UnreachableException(); } }
  public ModuleDefinition EnclosingModule { get { throw new cce.UnreachableException(); } }
  public bool MustReverify { get { throw new cce.UnreachableException(); } }
  public string FullSanitizedName { get { throw new cce.UnreachableException(); } }
  public bool AllowsNontermination { get { throw new cce.UnreachableException(); } }
  public IToken Tok { get { throw new cce.UnreachableException(); } }
  public IEnumerable<Node> Children => throw new cce.UnreachableException();

  public string GetDocstring(DafnyOptions options) {
    throw new cce.UnreachableException();
  }

  public string NameRelativeToModule { get { throw new cce.UnreachableException(); } }
  public Specification<Expression> Decreases { get { throw new cce.UnreachableException(); } }
  public bool InferredDecreases {
    get { throw new cce.UnreachableException(); }
    set { throw new cce.UnreachableException(); }
  }
  public bool AllowsAllocation => throw new cce.UnreachableException();
  public RangeToken RangeToken => throw new cce.UnreachableException();
}

/// <summary>
/// An IMethodCodeContext is a Method or IteratorDecl.
/// </summary>
public interface IMethodCodeContext : ICallable {
  List<Formal> Outs { get; }
  Specification<FrameExpression> Modifies { get; }
}

/// <summary>
/// Applies when we are not inside an ICallable.  In particular, a NoContext is used to resolve the attributes of declarations with no other context.
/// </summary>
public class NoContext : ICodeContext {
  public readonly ModuleDefinition Module;
  public NoContext(ModuleDefinition module) {
    this.Module = module;
  }
  bool ICodeContext.IsGhost { get { return true; } }
  List<TypeParameter> ICodeContext.TypeArgs { get { return new List<TypeParameter>(); } }
  List<Formal> ICodeContext.Ins { get { return new List<Formal>(); } }
  ModuleDefinition IASTVisitorContext.EnclosingModule { get { return Module; } }
  bool ICodeContext.MustReverify { get { Contract.Assume(false, "should not be called on NoContext"); throw new cce.UnreachableException(); } }
  public string FullSanitizedName { get { Contract.Assume(false, "should not be called on NoContext"); throw new cce.UnreachableException(); } }
  public bool AllowsNontermination { get { Contract.Assume(false, "should not be called on NoContext"); throw new cce.UnreachableException(); } }
  public bool AllowsAllocation => true;
}

public interface RedirectingTypeDecl : ICallable {
  string Name { get; }

  IToken tok { get; }
  IEnumerable<IToken> OwnedTokens { get; }
  IToken StartToken { get; }
  Attributes Attributes { get; }
  ModuleDefinition Module { get; }
  BoundVar/*?*/ Var { get; }
  Expression/*?*/ Constraint { get; }
  SubsetTypeDecl.WKind WitnessKind { get; }
  Expression/*?*/ Witness { get; }  // non-null iff WitnessKind is Compiled or Ghost
  FreshIdGenerator IdGenerator { get; }
}