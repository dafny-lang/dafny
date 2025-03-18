#nullable enable
using System.Collections.Generic;

namespace Microsoft.Dafny;

public abstract class TypeRhs : AssignmentRhs {

  [FilledInDuringResolution] public PreType? PreType;
  [FilledInDuringResolution] public Type? Type;

  protected TypeRhs(IOrigin origin, Attributes? attributes = null) : base(origin, attributes) {
  }

  protected TypeRhs(Cloner cloner, TypeRhs original)
    : base(cloner, original) {

    if (cloner.CloneResolvedFields) {
      Type = cloner.CloneType(original.Type);
    }
  }

  public IOrigin Start => Origin;


  public override IEnumerable<Statement> PreResolveSubStatements => [];
}