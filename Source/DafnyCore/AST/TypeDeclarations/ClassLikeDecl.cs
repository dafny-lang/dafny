using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class ClassLikeDecl : TopLevelDeclWithMembers, RevealableTypeDecl, ICanFormat, IHasDocstring, ICallable, ICanVerify {
  public NonNullTypeDecl NonNullTypeDecl; // returns non-null value iff IsReferenceTypeDecl

  public override bool CanBeRevealed() { return true; }

  public bool IsObjectTrait {
    get => Name == "object";
  }

  /// <summary>
  /// The IsReferenceTypeDecl getter must not be called before this information is available.
  /// For most types, this information is known immediately, but for a TraitDecl, the information is not known until
  /// SetUpAsReferenceType has been called. The SetUpAsReferenceType method is called very early during resolution,
  /// namely during name registration of the enclosing module.
  /// </summary>
  public abstract bool IsReferenceTypeDecl { get; }

  public TopLevelDecl AsTopLevelDecl => this;
  public TypeDeclSynonymInfo SynonymInfo { get; set; }

  public List<AttributedExpression> Invariants { get; }

  [SyntaxConstructor]
  protected ClassLikeDecl(IOrigin origin, Name nameNode, Attributes attributes,
    List<TypeParameter> typeArgs, ModuleDefinition enclosingModuleDefinition,
    [Captured] List<MemberDecl> members, List<Type> traits, List<AttributedExpression> invariants)
    : base(origin, nameNode, enclosingModuleDefinition, typeArgs, members, attributes, traits) {
    Contract.Requires(origin != null);
    Contract.Requires(nameNode != null);
    Contract.Requires(enclosingModuleDefinition != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(members));
   Invariants = invariants;
  }

  public virtual bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    IOrigin classToken = null;
    var parentTraitIndent = indentBefore + formatter.SpaceTab;
    var commaIndent = indentBefore;
    var extraIndent = 0;

    foreach (var token in OwnedTokens) {
      switch (token.val) {
        case "trait":
        case "class": {
            classToken = token;
            formatter.SetOpeningIndentedRegion(token, indentBefore);
            break;
          }
        case "extends": {
            if (token.line != token.Next.line) {
              extraIndent = classToken != null && classToken.line == token.line ? 0 : formatter.SpaceTab;
              commaIndent += extraIndent;
              formatter.SetIndentations(token, below: indentBefore + formatter.SpaceTab + extraIndent);
            } else {
              extraIndent += 2;
              commaIndent = indentBefore + formatter.SpaceTab;
              formatter.SetIndentations(token, below: indentBefore + formatter.SpaceTab);
            }

            break;
          }
        case ",": {
            formatter.SetIndentations(token, parentTraitIndent + extraIndent, commaIndent, parentTraitIndent + extraIndent);
            break;
          }
      }
    }

    Attributes.SetIndents(Attributes, indentBefore, formatter);

    foreach (var parent in Traits) {
      formatter.SetTypeIndentation(parent);
    }

    return true;
  }

  public virtual string GetTriviaContainingDocstring() {
    if (GetStartTriviaDocstring(out var triviaFound)) {
      return triviaFound;
    }

    foreach (var token in OwnedTokens) {
      if (token.val == "{") {
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

  public override string ReferenceName => base.ReferenceName + (IsReferenceTypeDecl ? "?" : "");
  
  // NB: largely copied from DatatypeDecl
  ModuleDefinition IASTVisitorContext.EnclosingModule => EnclosingModuleDefinition;
  bool ICodeContext.ContainsHide {
    get => throw new NotSupportedException();
    set => throw new NotSupportedException();
  }
  bool ICodeContext.IsGhost => true;
  List<TypeParameter> ICodeContext.TypeArgs => TypeArgs;
  List<Formal> ICodeContext.Ins => [];
  bool ICodeContext.MustReverify => false;
  bool ICodeContext.AllowsNontermination => false;
  CodeGenIdGenerator ICodeContext.CodeGenIdGenerator => CodeGenIdGenerator;
  string IFrameScope.Designator => WhatKind;
  string ICallable.NameRelativeToModule => Name;
  // See DatatypeDecl for why we don't implement these members
  Specification<Expression> ICallable.Decreases => throw new cce.UnreachableException();
  bool ICallable.InferredDecreases {
    get => throw new cce.UnreachableException();
    set => throw new cce.UnreachableException();
  }
  ModuleDefinition ICanVerify.ContainingModule => EnclosingModuleDefinition;
  bool ICanVerify.ShouldVerify => Invariants.Any();
}