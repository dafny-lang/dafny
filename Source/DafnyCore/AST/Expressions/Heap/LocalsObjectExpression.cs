using System.Collections.Generic;

namespace Microsoft.Dafny;

/// <summary>
/// Representation of the object containing the memory location of local variables.
/// Until we have the notion of unique object that cannot be moved, the following must hold
/// - It is NOT possible to read its fields directly.
///   It can be used only to describe memory locations. Reading the stack would require the stack to have its own
///   specialized "heap" as the actual memory locations are separated from the ones stored in the heap.
/// </summary>
public class LocalsObjectExpression : Expression, ICloneable<LocalsObjectExpression> {
  public LocalsObjectExpression(IOrigin origin) : base(origin) {
  }

  public LocalsObjectExpression(Cloner cloner, LocalsObjectExpression original) : base(cloner, original) {
  }

  public LocalsObjectExpression Clone(Cloner cloner) {
    return new LocalsObjectExpression(cloner, this);
  }
  public override IEnumerable<Expression> SubExpressions => [];
}