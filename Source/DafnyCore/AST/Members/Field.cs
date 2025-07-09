#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public class Field : MemberDecl, ICanFormat, IHasDocstring {
  public override string WhatKind => "field";

  public override bool HasStaticKeyword => false;
  public virtual bool IsMutable => true;  // says whether or not the field can ever change values
  public virtual bool IsUserMutable => true;  // says whether or not code is allowed to assign to the field (IsUserMutable implies IsMutable)

  public PreType? PreType;

  public Type Type;

  public Type? ExplicitType;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(!IsUserMutable || IsMutable);  // IsUserMutable ==> IsMutable
  }

  public override IEnumerable<INode> Children =>
    (Type?.Nodes ?? Enumerable.Empty<INode>()).Concat(this.Attributes.AsEnumerable());


  public Field(Cloner cloner, Field original) : base(cloner, original) {
    ExplicitType = cloner.CloneType(original.ExplicitType);
    // This is set even before resolution
    Type = cloner.CloneType(original.Type);
  }

  [SyntaxConstructor]
  public Field(IOrigin origin, Name nameNode, bool isGhost, Type? explicitType, Attributes? attributes)
    : base(origin, nameNode, isGhost, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(nameNode != null);
    ExplicitType = explicitType;
    Type = ExplicitType ?? new InferredTypeProxy();
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

  public string? GetTriviaContainingDocstring() {
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