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
  /// This property is used to determine if two module declarations have the same contents when doing resolution caching
  /// This should be replaced by using content hashes of module declaration contents, at which point this property
  /// becomes obsolete.
  /// </summary>
  public Guid CloneId { get; }

  public override string WhatKind => "module";

  [FilledInDuringResolution]
  public ModuleSignature Signature { get; set; }

  public virtual ModuleSignature AccessibleSignature(bool ignoreExports) {
    Contract.Requires(Signature != null);
    return Signature;
  }
  public virtual ModuleSignature AccessibleSignature() {
    Contract.Requires(Signature != null);
    return Signature;
  }
  public int Height;

  public readonly bool Opened; // TODO: Only true for Abstract and Alias module declarations. It seems like they need a common superclass since there's also code of the form 'd is AliasModuleDecl || d is AbstractModuleDecl'

  protected ModuleDecl(Cloner cloner, ModuleDecl original, ModuleDefinition parent)
    : base(cloner, original, parent) {
    Opened = original.Opened;
    CloneId = original.CloneId;
  }

  protected ModuleDecl(RangeToken rangeToken, Name name, ModuleDefinition parent, bool opened, bool isRefining, Guid cloneId)
    : base(rangeToken, name, parent, new List<TypeParameter>(), null, isRefining) {
    Height = -1;
    Signature = null;
    Opened = opened;
    CloneId = cloneId;
  }
  public abstract object Dereference();

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