using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ArrayClassDecl : ClassDecl {
  public override string WhatKind => "array type";

  public int Dims;
  public ArrayClassDecl(int dims, ModuleDefinition enclosingModule, Attributes attributes)
    : base(SourceOrigin.NoToken, new Name(SystemModuleManager.ArrayClassName(dims)), attributes,
      [new TypeParameter(SourceOrigin.NoToken, new Name("arg"), TPVarianceSyntax.NonVariant_Strict)],
      enclosingModule, [], [], false) {
    Contract.Requires(1 <= dims);
    Contract.Requires(enclosingModule != null);

    Dims = dims;
    // Resolve type parameter
    Contract.Assert(TypeArgs.Count == 1);
    var tp = TypeArgs[0];
    tp.Parent = this;
    tp.PositionalIndex = 0;
  }
}