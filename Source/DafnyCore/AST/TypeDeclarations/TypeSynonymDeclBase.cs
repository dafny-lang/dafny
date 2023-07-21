using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class TypeSynonymDeclBase : TopLevelDecl, RedirectingTypeDecl, IHasDocstring {
  public TypeParameter.TypeParameterCharacteristics Characteristics;  // the resolver may change the .EqualitySupport component of this value from Unspecified to InferredRequired (for some signatures that may immediately imply that equality support is required)
  public bool SupportsEquality {
    get { return Characteristics.EqualitySupport != TypeParameter.EqualitySupportValue.Unspecified; }
  }
  public readonly Type Rhs;

  protected TypeSynonymDeclBase(RangeToken rangeToken, Name name, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module, Type rhs, Attributes attributes)
    : base(rangeToken, name, module, typeArgs, attributes, false) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(typeArgs != null);
    Contract.Requires(module != null);
    Contract.Requires(rhs != null);
    Characteristics = characteristics;
    Rhs = rhs;
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

  public override IEnumerable<Node> Children => base.Children.Concat(
    Rhs != null ? new List<Node>() { Rhs } : Enumerable.Empty<Node>());

  string RedirectingTypeDecl.Name { get { return Name; } }
  IToken RedirectingTypeDecl.tok { get { return tok; } }
  IEnumerable<IToken> RedirectingTypeDecl.OwnedTokens => OwnedTokens;
  IToken RedirectingTypeDecl.StartToken => StartToken;
  Attributes RedirectingTypeDecl.Attributes { get { return Attributes; } }
  ModuleDefinition RedirectingTypeDecl.Module { get { return EnclosingModuleDefinition; } }
  BoundVar RedirectingTypeDecl.Var { get { return null; } }
  Expression RedirectingTypeDecl.Constraint { get { return null; } }
  SubsetTypeDecl.WKind RedirectingTypeDecl.WitnessKind { get { return SubsetTypeDecl.WKind.CompiledZero; } }
  Expression RedirectingTypeDecl.Witness { get { return null; } }
  FreshIdGenerator RedirectingTypeDecl.IdGenerator { get { return IdGenerator; } }

  bool ICodeContext.IsGhost {
    get { throw new NotSupportedException(); }  // if .IsGhost is needed, the object should always be wrapped in an CodeContextWrapper
  }
  List<TypeParameter> ICodeContext.TypeArgs { get { return TypeArgs; } }
  List<Formal> ICodeContext.Ins { get { return new List<Formal>(); } }
  ModuleDefinition IASTVisitorContext.EnclosingModule { get { return EnclosingModuleDefinition; } }
  bool ICodeContext.MustReverify { get { return false; } }
  bool ICodeContext.AllowsNontermination { get { return false; } }
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



  protected override string GetTriviaContainingDocstring() {
    IToken openingBlock = null;
    foreach (var token in OwnedTokens) {
      if (token.val == "{") {
        openingBlock = token;
      }
    }

    if (openingBlock != null && openingBlock.Prev.TrailingTrivia.Trim() != "") {
      return openingBlock.Prev.TrailingTrivia;
    }

    if (openingBlock == null && EndToken.TrailingTrivia.Trim() != "") {
      return EndToken.TrailingTrivia;
    }

    return GetTriviaContainingDocstringFromStartTokenOrNull();
  }
}