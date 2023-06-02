using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class Field : MemberDecl, ICanFormat, IHasDocstring {
  public override string WhatKind => "field";
  public readonly bool IsMutable;  // says whether or not the field can ever change values
  public readonly bool IsUserMutable;  // says whether or not code is allowed to assign to the field (IsUserMutable implies IsMutable)
  public PreType PreType;
  public readonly Type Type;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Type != null);
    Contract.Invariant(!IsUserMutable || IsMutable);  // IsUserMutable ==> IsMutable
  }

  public override IEnumerable<Node> Children => Type.Nodes;

  public Field(RangeToken rangeToken, Name name, bool isGhost, Type type, Attributes attributes)
    : this(rangeToken, name, false, isGhost, true, true, type, attributes) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(type != null);
  }

  public Field(RangeToken rangeToken, Name name, bool hasStaticKeyword, bool isGhost, bool isMutable, bool isUserMutable, Type type, Attributes attributes)
    : base(rangeToken, name, hasStaticKeyword, isGhost, attributes, false) {
    Contract.Requires(rangeToken != null);
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

  protected override string GetTriviaContainingDocstring() {
    if (EndToken.TrailingTrivia.Trim() != "") {
      return EndToken.TrailingTrivia;
    }

    return GetTriviaContainingDocstringFromStartTokenOrNull();
  }
}