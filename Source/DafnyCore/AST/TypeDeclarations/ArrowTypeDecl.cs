using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ArrowTypeDecl : ValuetypeDecl {
  public override string WhatKind => "function type";
  public readonly int Arity;
  public readonly Function Requires;
  public readonly Function Reads;

  public ArrowTypeDecl(List<TypeParameter> tps, Function req, Function reads, ModuleDefinition module, Attributes attributes)
    : base(ArrowType.ArrowTypeName(tps.Count - 1), module, tps,
      new List<MemberDecl> { req, reads }, attributes,
      ty =>
        ty.NormalizeExpandKeepConstraints() is UserDefinedType { ResolvedClass: ArrowTypeDecl arrowTypeDecl } && arrowTypeDecl.Arity == tps.Count - 1,
      null) {
    Contract.Requires(tps != null && 1 <= tps.Count);
    Contract.Requires(req != null);
    Contract.Requires(reads != null);
    Contract.Requires(module != null);
    Arity = tps.Count - 1;
    Requires = req;
    Reads = reads;
    Requires.EnclosingClass = this;
    Reads.EnclosingClass = this;
  }
}