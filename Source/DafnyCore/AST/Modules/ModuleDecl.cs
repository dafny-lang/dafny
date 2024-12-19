using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

/// <summary>
/// Represents a submodule declaration at module level scope
/// </summary>
public abstract class ModuleDecl : TopLevelDecl, IHasDocstring, ISymbol {

  public DafnyOptions Options { get; }

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
    Options = original.Options;
    Opened = original.Opened;
    CloneId = original.CloneId;
  }

  protected ModuleDecl(DafnyOptions options, IOrigin rangeOrigin, Name name, ModuleDefinition parent, bool opened, bool isRefining, Guid cloneId)
    : base(rangeOrigin, name, parent, new List<TypeParameter>(), null, isRefining) {
    Options = options;
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

  public virtual string GetTriviaContainingDocstring() {
    if (GetStartTriviaDocstring(out var triviaFound)) {
      return triviaFound;
    }
    var tokens = OwnedTokens.Any() ?
      OwnedTokens :
      PreResolveChildren.Any() ? PreResolveChildren.First().OwnedTokens : Enumerable.Empty<IOrigin>();
    foreach (var token in tokens) {
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

  public override SymbolKind? Kind => SymbolKind.Namespace;
  public override string GetDescription(DafnyOptions options) {
    return $"module {Name}";
  }
}