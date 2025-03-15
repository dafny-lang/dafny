using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class AbstractTypeDecl : TopLevelDeclWithMembers, RevealableTypeDecl, ICanFormat, IHasDocstring {
  public override string WhatKind { get { return "abstract type"; } }
  public override bool CanBeRevealed() { return true; }
  public TypeParameterCharacteristics Characteristics;
  public bool SupportsEquality {
    get { return Characteristics.EqualitySupport != TypeParameter.EqualitySupportValue.Unspecified; }
  }

  public AbstractTypeDecl(IOrigin origin, Name nameNode, ModuleDefinition enclosingModule, TypeParameterCharacteristics characteristics,
    List<TypeParameter> typeArgs, List<Type> parentTraits, List<MemberDecl> members, Attributes attributes, bool isRefining)
    : base(origin, nameNode, enclosingModule, typeArgs, members, attributes, parentTraits) {
    Contract.Requires(origin != null);
    Contract.Requires(nameNode != null);
    Contract.Requires(enclosingModule != null);
    Contract.Requires(typeArgs != null);
    IsRefining = isRefining;
    Characteristics = characteristics;
    this.NewSelfSynonym();
  }

  public override bool IsRefining { get; }

  public TopLevelDecl AsTopLevelDecl => this;
  public TypeDeclSynonymInfo SynonymInfo { get; set; }
  public override bool AcceptThis => true;
  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var indent2 = indentBefore + formatter.SpaceTab;
    var typeArgumentIndent = indent2;
    var commaIndent = indent2;
    var rightIndent = indent2;
    Attributes.SetIndents(Attributes, indentBefore, formatter);
    foreach (var token in OwnedTokens) {
      switch (token.val) {
        case "type": {
            formatter.SetOpeningIndentedRegion(token, indentBefore);
            break;
          }
        case "=": {
            if (TokenNewIndentCollector.IsFollowedByNewline(token)) {
              formatter.SetDelimiterInsideIndentedRegions(token, indent2);
            } else {
              formatter.SetAlign(indent2, token, out typeArgumentIndent, out _);
            }

            break;
          }
        case "<": {
            if (TokenNewIndentCollector.IsFollowedByNewline(token)) {
              formatter.SetOpeningIndentedRegion(token, typeArgumentIndent);
              commaIndent = typeArgumentIndent;
              rightIndent = commaIndent + formatter.SpaceTab;
            } else {
              formatter.SetAlign(typeArgumentIndent + formatter.SpaceTab, token, out rightIndent, out commaIndent);
            }

            break;
          }
        case ">": {
            formatter.SetIndentations(token.Prev, below: rightIndent);
            formatter.SetClosingIndentedRegionAligned(token, rightIndent, typeArgumentIndent);
            break;
          }
        case ",": {
            formatter.SetIndentations(token, rightIndent, commaIndent, rightIndent);
            break;
          }
        case ";": {
            break;
          }
        case "{": {
            formatter.SetOpeningIndentedRegion(token, indentBefore);
            break;
          }
        case "}": {
            formatter.SetClosingIndentedRegion(token, indentBefore);
            break;
          }
      }
    }

    if (EndToken.TrailingTrivia.Trim() == "") {
      formatter.SetIndentations(EndToken, below: indentBefore);
    }

    return true;
  }

  public string GetTriviaContainingDocstring() {
    if (GetStartTriviaDocstring(out var triviaFound)) {
      return triviaFound;
    }
    Token openingBlock = null;
    foreach (var token in OwnedTokens) {
      if (token.val == "{") {
        openingBlock = token;
      }
    }

    var tentativeTrivia = "";
    if (openingBlock != null) {
      tentativeTrivia = (openingBlock.Prev.TrailingTrivia + openingBlock.LeadingTrivia).Trim();
      if (tentativeTrivia != "") {
        return tentativeTrivia;
      }
    }

    tentativeTrivia = EndToken.TrailingTrivia.Trim();
    if (tentativeTrivia != "") {
      return tentativeTrivia;
    }

    return null;
  }
}