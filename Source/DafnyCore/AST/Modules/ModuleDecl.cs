using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// Represents a submodule declaration at module level scope
/// </summary>
public abstract class ModuleDecl : TopLevelDecl, IHasDocstring {
  public override string WhatKind { get { return "module"; } }
  [FilledInDuringResolution] public ModuleSignature Signature; // filled in topological order.
  public virtual ModuleSignature AccessibleSignature(bool ignoreExports) {
    Contract.Requires(Signature != null);
    return Signature;
  }
  public virtual ModuleSignature AccessibleSignature() {
    Contract.Requires(Signature != null);
    return Signature;
  }
  public int Height;

  public readonly bool Opened;

  public ModuleDecl(RangeToken rangeToken, Name name, ModuleDefinition parent, bool opened, bool isRefining)
    : base(rangeToken, name, parent, new List<TypeParameter>(), null, isRefining) {
    Height = -1;
    Signature = null;
    Opened = opened;
  }
  public abstract object Dereference();

  public int? ResolvedHash { get; set; }

  public override bool IsEssentiallyEmpty() {
    // A module or import is considered "essentially empty" to its parents, but the module is going to be resolved by itself.
    return true;
  }

  protected override string GetTriviaContainingDocstring() {
    IToken candidate = null;
    var tokens = OwnedTokens.Any() ?
      OwnedTokens :
      PreResolveChildren.Any() ? PreResolveChildren.First().OwnedTokens : Enumerable.Empty<IToken>();
    foreach (var token in tokens) {
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