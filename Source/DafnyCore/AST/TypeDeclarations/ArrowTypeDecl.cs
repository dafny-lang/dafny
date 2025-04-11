using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ArrowTypeDecl : ValuetypeDecl {
  public override string WhatKind => "function type";
  public int Arity;
  public Function Requires;
  public Function Reads;

  public ArrowTypeDecl(List<TypeParameter> tps, Function req, Function reads, ModuleDefinition enclosingModule, Attributes attributes)
    : base(ArrowType.ArrowTypeName(tps.Count - 1), enclosingModule, tps,
      [req, reads], attributes,
      ty =>
        ty.NormalizeExpandKeepConstraints() is UserDefinedType { ResolvedClass: ArrowTypeDecl arrowTypeDecl } && arrowTypeDecl.Arity == tps.Count - 1,
      null) {
    Contract.Requires(tps != null && 1 <= tps.Count);
    Contract.Requires(req != null);
    Contract.Requires(reads != null);
    Contract.Requires(enclosingModule != null);
    Arity = tps.Count - 1;
    Requires = req;
    Reads = reads;
    Requires.EnclosingClass = this;
    Reads.EnclosingClass = this;
  }
}