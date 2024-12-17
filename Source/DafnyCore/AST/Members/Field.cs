using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public class Field : MemberDecl, ICanFormat, IHasDocstring {
  public override string WhatKind => "field";
  public readonly bool IsMutable;  // says whether or not the field can ever change values
  public readonly bool IsUserMutable;  // says whether or not code is allowed to assign to the field (IsUserMutable implies IsMutable)
  public PreType PreType;

  public readonly Type Type; // Might be null after parsing and set during resolution
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Type != null);
    Contract.Invariant(!IsUserMutable || IsMutable);  // IsUserMutable ==> IsMutable
  }

  public override IEnumerable<INode> Children =>
    (Type?.Nodes ?? Enumerable.Empty<INode>()).Concat(this.Attributes.AsEnumerable());

  public Field(IOrigin rangeOrigin, Name name, bool isGhost, Type type, Attributes attributes)
    : this(rangeOrigin, name, false, isGhost, true, true, type, attributes) {
    Contract.Requires(rangeOrigin != null);
    Contract.Requires(name != null);
    Contract.Requires(type != null);
  }

  public Field(IOrigin rangeOrigin, Name name, bool hasStaticKeyword, bool isGhost, bool isMutable, bool isUserMutable, Type type, Attributes attributes)
    : base(rangeOrigin, name, hasStaticKeyword, isGhost, attributes, false) {
    Contract.Requires(rangeOrigin != null);
    Contract.Requires(name != null);
    Contract.Requires(type != null);
    Contract.Requires(!isUserMutable || isMutable);
    IsMutable = isMutable;
    IsUserMutable = isUserMutable;
    Type = type;
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    formatter.SetOpeningIndentedRegion(StartToken, indentBefore);
    formatter.SetIndentations(EndToken, below: indentBefore);
    Attributes.SetIndents(Attributes, indentBefore, formatter);
    var hasComma = OwnedTokens.Any(token => token.val == ",");
    switch (this) {
      case ConstantField constantField:
        var ownedTokens = constantField.OwnedTokens;
        var commaIndent = indentBefore + formatter.SpaceTab;
        var rightIndent = indentBefore + formatter.SpaceTab;
        foreach (var token in ownedTokens) {
          switch (token.val) {
            case ":=": {
                if (TokenNewIndentCollector.IsFollowedByNewline(token)) {
                  formatter.SetDelimiterInsideIndentedRegions(token, indentBefore);
                } else if (formatter.ReduceBlockiness && token.Next.val is "{" or "[" or "(") {
                  if (!hasComma) {
                    rightIndent = indentBefore;
                    commaIndent = indentBefore;
                  } else {
                    rightIndent = indentBefore + formatter.SpaceTab;
                    commaIndent = indentBefore + formatter.SpaceTab;
                  }

                  formatter.SetIndentations(token, indentBefore, indentBefore, rightIndent);
                } else {
                  formatter.SetAlign(indentBefore + formatter.SpaceTab, token, out rightIndent, out commaIndent);
                }

                break;
              }
            case ",": {
                formatter.SetIndentations(token, rightIndent, commaIndent, rightIndent);
                break;
              }
            case ";": {
                break;
              }
          }
        }

        if (constantField.Rhs is { } constantFieldRhs) {
          formatter.SetExpressionIndentation(constantFieldRhs);
        }

        break;
    }

    return true;
  }

  public string GetTriviaContainingDocstring() {
    if (GetStartTriviaDocstring(out var triviaFound)) {
      return triviaFound;
    }
    foreach (var token in OwnedTokens) {
      if (token.val == ":=") {
        if ((token.Prev.TrailingTrivia + (token.LeadingTrivia ?? "")).Trim() is { } tentativeTrivia and not "") {
          return tentativeTrivia;
        }
      }
    }
    if (EndToken.TrailingTrivia.Trim() is { } tentativeTrivia2 and not "") {
      return tentativeTrivia2;
    }

    return null;
  }

  public override SymbolKind? Kind => SymbolKind.Field;

  public override string GetDescription(DafnyOptions options) {
    var prefix = IsMutable ? "var" : "const";
    return $"{prefix} {AstExtensions.GetMemberQualification(this)}{Name}: {Type}";
  }
}