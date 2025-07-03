using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public abstract class DatatypeDecl : TopLevelDeclWithMembers, RevealableTypeDecl, ICallable, ICanFormat, IHasDocstring, ICanAutoRevealDependencies {
  public override bool CanBeRevealed() { return true; }
  public List<DatatypeCtor> Ctors;

  [FilledInDuringResolution] public Dictionary<string, DatatypeCtor> ConstructorsByName { get; set; }
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Cce.NonNullElements(Ctors));
    Contract.Invariant(1 <= Ctors.Count);
  }

  public override IEnumerable<INode> Children => Ctors.Concat(base.Children);

  public override IEnumerable<INode> PreResolveChildren => Ctors.Concat(base.PreResolveChildren);

  [SyntaxConstructor]
  protected DatatypeDecl(IOrigin origin, Name nameNode, ModuleDefinition enclosingModuleDefinition, List<TypeParameter> typeArgs,
    [Captured] List<DatatypeCtor> ctors, List<Type> traits, List<MemberDecl> members, Attributes attributes, bool isRefining)
    : base(origin, nameNode, enclosingModuleDefinition, typeArgs, members, attributes, traits) {
    Contract.Requires(origin != null);
    Contract.Requires(nameNode != null);
    Contract.Requires(enclosingModuleDefinition != null);
    Contract.Requires(Cce.NonNullElements(typeArgs));
    Contract.Requires(Cce.NonNullElements(ctors));
    Contract.Requires(Cce.NonNullElements(members));
    Contract.Requires((isRefining && ctors.Count == 0) || (!isRefining && 1 <= ctors.Count));
    Ctors = ctors;
    this.NewSelfSynonym();
    IsRefining = isRefining;
  }

  public override bool IsRefining { get; }

  public bool HasFinitePossibleValues {
    get {
      // Note, to determine finiteness, it doesn't matter if the constructors are ghost or non-ghost.
      return (TypeArgs.Count == 0 && Ctors.TrueForAll(ctr => ctr.Formals.Count == 0));
    }
  }

  public bool IsRecordType {
    get { return this is IndDatatypeDecl && Ctors.Count == 1 && !Ctors[0].IsGhost; }
  }

  public bool HasGhostVariant => Ctors.Any(ctor => ctor.IsGhost);

  public TopLevelDecl AsTopLevelDecl => this;
  public TypeDeclSynonymInfo SynonymInfo { get; set; }

  public bool ContainsHide {
    get => throw new NotSupportedException();
    set => throw new NotSupportedException();
  }

  bool ICodeContext.IsGhost { get { return true; } }
  List<TypeParameter> ICodeContext.TypeArgs { get { return TypeArgs; } }
  List<Formal> ICodeContext.Ins { get { return []; } }
  ModuleDefinition IASTVisitorContext.EnclosingModule { get { return EnclosingModuleDefinition; } }
  bool ICodeContext.MustReverify { get { return false; } }
  bool ICodeContext.AllowsNontermination { get { return false; } }
  CodeGenIdGenerator ICodeContext.CodeGenIdGenerator => CodeGenIdGenerator;
  string ICallable.NameRelativeToModule { get { return Name; } }
  Specification<Expression> ICallable.Decreases {
    get {
      // The resolver checks that a NewtypeDecl sits in its own SSC in the call graph.  Therefore,
      // the question of what its Decreases clause is should never arise.
      throw new Cce.UnreachableException();
    }
  }
  bool ICallable.InferredDecreases {
    get { throw new Cce.UnreachableException(); }  // see comment above about ICallable.Decreases
    set { throw new Cce.UnreachableException(); }  // see comment above about ICallable.Decreases
  }

  /// <summary>
  /// For information about the grounding constructor, see docs/Compilation/AutoInitialization.md.
  /// </summary>
  public abstract DatatypeCtor GetGroundingCtor();


  public override bool IsEssentiallyEmpty() {
    if (Ctors.Any(ctor => ctor.Attributes != null || ctor.Formals.Count != 0)) {
      return false;
    }
    return base.IsEssentiallyEmpty();
  }

  public override IEnumerable<ISymbol> ChildSymbols => base.ChildSymbols.Concat(Ctors);
  public override SymbolKind? Kind => SymbolKind.Enum;

  public bool SetIndent(int indent, TokenNewIndentCollector formatter) {
    Attributes.SetIndents(Attributes, indent, formatter);

    var indent2 = indent + formatter.SpaceTab;
    var verticalBarIndent = indent2;
    var rightOfVerticalBarIndent = indent2 + formatter.SpaceTab;
    if (OwnedTokens.All(token =>
          token.val != "|" || TokenNewIndentCollector.IsFollowedByNewline(token) || token.Next.line == token.Prev.line)) {
      rightOfVerticalBarIndent = indent2;
    }

    var commaIndent = indent2;
    var rightIndent = indent2;
    var noExtraIndent =
      formatter.ReduceBlockiness && Ctors.Count == 1
                                 && Ctors[0].Formals.Count > 0
                                 && Ctors[0].StartToken.line == StartToken.line;
    if (noExtraIndent) {
      rightOfVerticalBarIndent = indent;
    }

    var ownedTokens = OwnedTokens.Concat(this.Ctors.SelectMany(ctor => ctor.OwnedTokens))
      .OrderBy(token => token.pos);
    foreach (var token in ownedTokens) {
      switch (token.val) {
        case "codatatype":
        case "datatype": {
            formatter.SetOpeningIndentedRegion(token, indent);
            break;
          }
        case "=": {
            if (TokenNewIndentCollector.IsFollowedByNewline(token) || noExtraIndent) {
              formatter.SetIndentations(token, rightOfVerticalBarIndent, indent + formatter.SpaceTab, rightOfVerticalBarIndent);
            } else {
              formatter.SetAlign(indent2, token, out rightOfVerticalBarIndent, out verticalBarIndent);
            }

            break;
          }
        case "|": {
            formatter.SetIndentations(token, rightOfVerticalBarIndent, verticalBarIndent, rightOfVerticalBarIndent);
            break;
          }
        case "(": {
            if (TokenNewIndentCollector.IsFollowedByNewline(token)) {
              formatter.SetOpeningIndentedRegion(token, rightOfVerticalBarIndent);
              commaIndent = rightOfVerticalBarIndent;
              rightIndent = commaIndent + formatter.SpaceTab;
            } else {
              formatter.SetAlign(rightOfVerticalBarIndent + formatter.SpaceTab, token, out rightIndent, out commaIndent);
            }

            break;
          }
        case ")": {
            formatter.SetIndentations(token.Prev, below: rightIndent);
            formatter.SetClosingIndentedRegionAligned(token, rightIndent, rightOfVerticalBarIndent);
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
            formatter.SetOpeningIndentedRegion(token, indent);
            break;
          }
        case "}": {
            formatter.SetClosingIndentedRegion(token, indent);
            break;
          }
      }
    }

    foreach (var ctor in this.Ctors) {
      formatter.SetFormalsIndentation(ctor.Formals);
    }

    if (EndToken.TrailingTrivia.Trim() == "") {
      formatter.SetIndentations(this.EndToken, below: indent);
    }

    return true;
  }

  public string GetTriviaContainingDocstring() {
    if (GetStartTriviaDocstring(out var triviaFound)) {
      return triviaFound;
    }
    foreach (var token in OwnedTokens) {
      if (token.val == "=") {
        if ((token.Prev.TrailingTrivia + (token.LeadingTrivia ?? "")).Trim() is { } tentativeTrivia and not "") {
          return tentativeTrivia;
        }
      }
    }

    return null;
  }

  public void AutoRevealDependencies(AutoRevealFunctionDependencies Rewriter, DafnyOptions Options, ErrorReporter Reporter) {
    foreach (var ctor in Ctors) {
      foreach (var formal in ctor.Formals) {
        if (formal.DefaultValue is null) {
          continue;
        }

        var addedReveals = Rewriter.ExprToFunctionalDependencies(formal.DefaultValue, EnclosingModuleDefinition);
        formal.DefaultValue = Rewriter.AddRevealStmtsToExpression(formal.DefaultValue, addedReveals);

        if (addedReveals.Any()) {
          Reporter.Message(MessageSource.Rewriter, ErrorLevel.Info, null, formal.Origin,
            AutoRevealFunctionDependencies.GenerateMessage(addedReveals.ToList()));
        }
      }
    }
  }
  public string Designator => WhatKind;
}