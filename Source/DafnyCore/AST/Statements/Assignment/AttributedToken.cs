using System.Security.Policy;

namespace Microsoft.Dafny;

/// <summary>
/// Attributed tokens are used when a subpart of a statement or expression can take attributes.
/// (Perhaps in addition to attributes placed on the token itself.)
///
/// It is used in particular to attach `{:axiom}` tokens to the `assume` keyword
/// on the RHS of `:|` and `:-` (in contrast, for `assume` statements, the
/// `{:axiom}` attribute is directly attached to the statement-level
/// attributes).
/// </summary>
public record AttributedToken(IOrigin Token, Attributes Attrs) : IAttributeBearingDeclaration {
  Attributes IAttributeBearingDeclaration.Attributes {
    get => Attrs;
    set => throw new System.NotImplementedException();
  }
  string IAttributeBearingDeclaration.WhatKind => "token";
}