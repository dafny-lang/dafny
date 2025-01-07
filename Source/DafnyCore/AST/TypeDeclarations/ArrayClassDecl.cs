using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ArrayClassDecl : ClassDecl {
  public override string WhatKind => "array type";

  public readonly int Dims;
  public ArrayClassDecl(int dims, ModuleDefinition module, Attributes attrs)
    : base(SourceOrigin.NoToken, new Name(SystemModuleManager.ArrayClassName(dims)), module,
      new List<TypeParameter>(new TypeParameter[] { new TypeParameter(SourceOrigin.NoToken, new Name("arg"), TypeParameter.TPVarianceSyntax.NonVariant_Strict) }),
      new List<MemberDecl>(), attrs, false, null) {
    Contract.Requires(1 <= dims);
    Contract.Requires(module != null);

    Dims = dims;
    // Resolve type parameter
    Contract.Assert(TypeArgs.Count == 1);
    var tp = TypeArgs[0];
    tp.Parent = this;
    tp.PositionalIndex = 0;
  }
}