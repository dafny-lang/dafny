using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public abstract class ClassLikeDecl : TopLevelDeclWithMembers, RevealableTypeDecl, ICanFormat {
  public NonNullTypeDecl NonNullTypeDecl; // returns non-null value iff IsReferenceTypeDecl

  public bool IsObjectTrait {
    get => Name == "object";
  }
  public abstract bool IsReferenceTypeDecl { get; }

  public TopLevelDecl AsTopLevelDecl => this;
  public TypeDeclSynonymInfo SynonymInfo { get; set; }

  public ClassLikeDecl(RangeToken rangeToken, Name name, ModuleDefinition module,
    List<TypeParameter> typeArgs, [Captured] List<MemberDecl> members, Attributes attributes, bool isRefining, List<Type>/*?*/ traits)
    : base(rangeToken, name, module, typeArgs, members, attributes, isRefining, traits) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(members));
  }

  public virtual bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    IToken classToken = null;
    var parentTraitIndent = indentBefore + formatter.SpaceTab;
    var commaIndent = indentBefore;
    var extraIndent = 0;

    foreach (var token in OwnedTokens) {
      switch (token.val) {
        case "class": {
            classToken = token;
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

    foreach (var parent in ParentTraits) {
      formatter.SetTypeIndentation(parent);
    }

    return true;
  }

  public List<Type> PossiblyNullTraitsWithArgument(List<Type> typeArgs) {
    Contract.Requires(typeArgs != null);
    Contract.Requires(typeArgs.Count == TypeArgs.Count);
    // Instantiate with the actual type arguments
    var subst = TypeParameter.SubstitutionMap(TypeArgs, typeArgs);
    return ParentTraits.ConvertAll(traitType => (Type)UserDefinedType.CreateNullableType((UserDefinedType)traitType.Subst(subst)));
  }

  public override List<Type> ParentTypes(List<Type> typeArgs) {
    return PossiblyNullTraitsWithArgument(typeArgs);
  }

  protected override string GetTriviaContainingDocstring() {
    IToken candidate = null;
    foreach (var token in OwnedTokens) {
      if (token.val == "{") {
        candidate = token.Prev;
        if (candidate.TrailingTrivia.Trim() != "") {
          return candidate.TrailingTrivia;
        }
      }
    }

    if (candidate == null && EndToken.TrailingTrivia.Trim() != "") {
      return EndToken.TrailingTrivia;
    }

    return GetTriviaContainingDocstringFromStartTokenOrNull();
  }
}