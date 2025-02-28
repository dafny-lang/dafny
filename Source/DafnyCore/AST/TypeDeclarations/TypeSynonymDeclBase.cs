using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public abstract class TypeSynonymDeclBase : TopLevelDecl, RedirectingTypeDecl, IHasDocstring {
  public TypeParameterCharacteristics Characteristics;  // the resolver may change the .EqualitySupport component of this value from Unspecified to InferredRequired (for some signatures that may immediately imply that equality support is required)
  public bool SupportsEquality {
    get { return Characteristics.EqualitySupport != TypeParameter.EqualitySupportValue.Unspecified; }
  }
  public abstract Type Rhs { get; }

  [SyntaxConstructor]
  protected TypeSynonymDeclBase(IOrigin origin, Name nameNode, TypeParameterCharacteristics characteristics,
    List<TypeParameter> typeArgs, ModuleDefinition enclosingModuleDefinition, Attributes attributes)
    : base(origin, nameNode, enclosingModuleDefinition, typeArgs, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(typeArgs != null);
    Characteristics = characteristics;
  }
  /// <summary>
  /// Return .Rhs instantiated with "typeArgs", but only look at the part of .Rhs that is in scope.
  /// </summary>
  public Type RhsWithArgument(List<Type> typeArgs) {
    Contract.Requires(typeArgs != null);
    Contract.Requires(typeArgs.Count == TypeArgs.Count);
    var scope = Type.GetScope();
    var rtd = Rhs.AsRevealableType;
    if (rtd != null) {
      Contract.Assume(rtd.AsTopLevelDecl.IsVisibleInScope(scope));
      if (!rtd.IsRevealedInScope(scope)) {
        // type is actually hidden in this scope
        return rtd.SelfSynonym(typeArgs);
      }
    }
    return RhsWithArgumentIgnoringScope(typeArgs);
  }
  /// <summary>
  /// Returns the declared .Rhs but with formal type arguments replaced by the given actuals.
  /// </summary>
  public Type RhsWithArgumentIgnoringScope(List<Type> typeArgs) {
    Contract.Requires(typeArgs != null);
    Contract.Requires(typeArgs.Count == TypeArgs.Count);
    // Instantiate with the actual type arguments
    if (typeArgs.Count == 0) {
      // this optimization seems worthwhile
      return Rhs;
    } else {
      var subst = TypeParameter.SubstitutionMap(TypeArgs, typeArgs);
      return Rhs.Subst(subst);
    }
  }

  public override IEnumerable<INode> Children => base.Children.Concat(
    Rhs != null ? new List<Node>() { Rhs } : Enumerable.Empty<Node>());

  string RedirectingTypeDecl.Name { get { return Name; } }
  IOrigin RedirectingTypeDecl.Tok { get { return Origin; } }
  Attributes RedirectingTypeDecl.Attributes { get { return Attributes; } }
  ModuleDefinition RedirectingTypeDecl.Module { get { return EnclosingModuleDefinition; } }
  BoundVar RedirectingTypeDecl.Var { get { return null; } }
  PreType RedirectingTypeDecl.BasePreType { get { return null; } }
  Type RedirectingTypeDecl.BaseType { get { return null; } }
  Expression RedirectingTypeDecl.Constraint { get { return null; } }

  bool RedirectingTypeDecl.ConstraintIsCompilable {
    get => throw new NotSupportedException();
    set => throw new NotSupportedException();
  }

  SubsetTypeDecl.WKind RedirectingTypeDecl.WitnessKind { get { return SubsetTypeDecl.WKind.CompiledZero; } }
  Expression RedirectingTypeDecl.Witness { get { return null; } }
  VerificationIdGenerator RedirectingTypeDecl.IdGenerator { get { return IdGenerator; } }

  public bool ContainsHide { get; set; }

  bool ICodeContext.IsGhost => throw new NotSupportedException(); // if .IsGhost is needed, the object should always be wrapped in an CodeContextWrapper
  List<TypeParameter> ICodeContext.TypeArgs => TypeArgs;
  List<Formal> ICodeContext.Ins => [];
  ModuleDefinition IASTVisitorContext.EnclosingModule { get { return EnclosingModuleDefinition; } }
  bool ICodeContext.MustReverify { get { return false; } }
  bool ICodeContext.AllowsNontermination { get { return false; } }
  CodeGenIdGenerator ICodeContext.CodeGenIdGenerator => CodeGenIdGenerator;
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
  public override bool CanBeRevealed() {
    return true;
  }

  public override bool IsEssentiallyEmpty() {
    // A synonym/subset type is not considered "essentially empty", because it always has a parent type to be resolved.
    return false;
  }

  public string GetTriviaContainingDocstring() {
    if (GetStartTriviaDocstring(out var triviaFound)) {
      return triviaFound;
    }

    foreach (var token in OwnedTokens) {
      if (token.val == "=") {
        if ((token.Prev.TrailingTrivia + token.LeadingTrivia).Trim() is { } tentativeTrivia and not "") {
          return tentativeTrivia;
        }
      }
    }

    if (EndToken.TrailingTrivia.Trim() is { } tentativeTrivia2 and not "") {
      return tentativeTrivia2;
    }

    return null;
  }

  public abstract override SymbolKind? Kind { get; }
  public abstract override string GetDescription(DafnyOptions options);
  public string Designator => WhatKind;
}