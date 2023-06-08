using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// Represents a submodule declaration at module level scope
/// </summary>
public abstract class ModuleDecl : TopLevelDecl, IHasDocstring {
  /// <summary>
  /// Only equivalent between modules if one is a clone of the other.
  /// </summary>
  public Guid CloneId { get; set; } = Guid.NewGuid();

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

  protected ModuleDecl(Cloner cloner, ModuleDecl original) : base(cloner, original) {
    Opened = original.Opened;
    CloneId = original.CloneId;
  }

  protected ModuleDecl(RangeToken rangeToken, Name name, ModuleDefinition enclosingModule, List<TypeParameter> typeArgs,
    Attributes attributes, bool isRefining)
    : base(rangeToken, name, enclosingModule, typeArgs, attributes, isRefining) {
  }

  protected ModuleDecl(RangeToken rangeToken, Name name, ModuleDefinition parent, bool opened, bool isRefining)
    : base(rangeToken, name, parent, new List<TypeParameter>(), null, isRefining) {
    Height = -1;
    Signature = null;
    Opened = opened;
  }
  public abstract object Dereference();

  public int? ResolvedHash { get; set; } // TODO never set, so remove.

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