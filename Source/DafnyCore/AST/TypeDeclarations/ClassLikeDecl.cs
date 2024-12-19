using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class ClassLikeDecl : TopLevelDeclWithMembers, RevealableTypeDecl, ICanFormat, IHasDocstring {
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

  public ClassLikeDecl(IOrigin rangeOrigin, Name name, ModuleDefinition module,
    List<TypeParameter> typeArgs, [Captured] List<MemberDecl> members, Attributes attributes, bool isRefining, List<Type>/*?*/ traits)
    : base(rangeOrigin, name, module, typeArgs, members, attributes, isRefining, traits) {
    Contract.Requires(rangeOrigin != null);
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(members));
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

    foreach (var parent in ParentTraits) {
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
}