using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

/// <summary>
/// An ICodeContext is an ICallable or a NoContext.
/// </summary>
public interface ICodeContext : IASTVisitorContext {
  bool ContainsHide { get; set; }
  bool IsGhost { get; }
  List<TypeParameter> TypeArgs { get; }
  List<Formal> Ins { get; }
  bool MustReverify { get; }
  string FullSanitizedName { get; }
  bool AllowsNontermination { get; }
  CodeGenIdGenerator CodeGenIdGenerator { get; }
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

  public bool ContainsHide {
    get => inner.ContainsHide;
    set => inner.ContainsHide = value;
  }

  public bool IsGhost => isGhostContext;
  public List<TypeParameter> TypeArgs => inner.TypeArgs;
  public List<Formal> Ins => inner.Ins;
  public ModuleDefinition EnclosingModule => inner.EnclosingModule;
  public bool MustReverify => inner.MustReverify;
  public string FullSanitizedName => inner.FullSanitizedName;
  public bool AllowsNontermination => inner.AllowsNontermination;
  CodeGenIdGenerator ICodeContext.CodeGenIdGenerator => inner.CodeGenIdGenerator;

  public static ICodeContext Unwrap(ICodeContext codeContext) {
    while (codeContext is CodeContextWrapper ccw) {
      codeContext = ccw.inner;
    }
    return codeContext;
  }
}

interface ICodeContainer {
}

/// <summary>
/// An ICallable is a Function, Method, IteratorDecl, or (less fitting for the name ICallable) RedirectingTypeDecl or DatatypeDecl.
/// </summary>
public interface ICallable : ICodeContext, ISymbol, IFrameScope {
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

  public ICallable CwInner => (ICallable)inner;
  public IOrigin Tok => CwInner.Tok;
  public IEnumerable<INode> Children => CwInner.Children;
  public IEnumerable<INode> PreResolveChildren => CwInner.PreResolveChildren;

  public string WhatKind => CwInner.WhatKind;
  public string NameRelativeToModule => CwInner.NameRelativeToModule;
  public Specification<Expression> Decreases => CwInner.Decreases;

  public bool InferredDecreases {
    get => CwInner.InferredDecreases;
    set { CwInner.InferredDecreases = value; }
  }

  public bool AllowsAllocation => CwInner.AllowsAllocation;

  public bool SingleFileToken => CwInner.SingleFileToken;
  public IEnumerable<IOrigin> OwnedTokens => CwInner.OwnedTokens;
  public IOrigin Origin => CwInner.Origin;
  public IOrigin NavigationToken => CwInner.NavigationToken;
  public SymbolKind? Kind => CwInner.Kind;
  public string GetDescription(DafnyOptions options) {
    return CwInner.GetDescription(options);
  }

  public string Designator => WhatKind;
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

  public bool ContainsHide {
    get => throw new NotSupportedException();
    set => throw new NotSupportedException();
  }
  bool ICodeContext.IsGhost { get { return true; } }
  List<TypeParameter> ICodeContext.TypeArgs { get { return new List<TypeParameter>(); } }
  List<Formal> ICodeContext.Ins { get { return new List<Formal>(); } }
  ModuleDefinition IASTVisitorContext.EnclosingModule { get { return Module; } }
  bool ICodeContext.MustReverify { get { Contract.Assume(false, "should not be called on NoContext"); throw new cce.UnreachableException(); } }
  public string FullSanitizedName { get { Contract.Assume(false, "should not be called on NoContext"); throw new cce.UnreachableException(); } }
  public bool AllowsNontermination { get { Contract.Assume(false, "should not be called on NoContext"); throw new cce.UnreachableException(); } }
  CodeGenIdGenerator ICodeContext.CodeGenIdGenerator { get; } = new();

  public bool AllowsAllocation => true;
}

public interface RedirectingTypeDecl : ICallable {
  string Name { get; }

  string FullDafnyName { get; }

  Attributes Attributes { get; }
  ModuleDefinition Module { get; }
  BoundVar/*?*/ Var { get; }
  PreType BasePreType { get; }
  Type BaseType { get; }
  Expression/*?*/ Constraint { get; }
  SubsetTypeDecl.WKind WitnessKind { get; }
  Expression/*?*/ Witness { get; }  // non-null iff WitnessKind is Compiled or Ghost
  VerificationIdGenerator IdGenerator { get; }

  [FilledInDuringResolution] bool ConstraintIsCompilable { get; set; }
}