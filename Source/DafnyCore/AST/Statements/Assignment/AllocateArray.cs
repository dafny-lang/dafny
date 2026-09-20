#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// At most one of ElementInit and InitDisplay may be non-null
/// </summary>
public class AllocateArray : TypeRhs, ICloneable<AllocateArray> {
  public Type? ExplicitType;
  public readonly List<Expression> ArrayDimensions;
  public readonly Expression? ElementInit;
  public readonly List<Expression>? InitDisplay;

  /// <summary>
  /// Non-null exactly when <see cref="ExplicitType"/> is null, so that
  /// <see cref="ElementType"/> always has something to return.
  /// </summary>
  private readonly Type? inferredElementType;

  /// <summary>
  /// The element type resolution works on: the type the user wrote, when there is one, and
  /// otherwise a proxy for resolution to fill in. When the user wrote one this must be the very
  /// same object as <see cref="ExplicitType"/>, since that is what the resolver resolves, in
  /// place; returning ExplicitType itself is what makes that hold. Compare
  /// NonglobalVariable.SafeSyntacticType.
  /// </summary>
  public Type ElementType => ExplicitType ?? inferredElementType!;

  [SyntaxConstructor]
  public AllocateArray(IOrigin origin, Type? explicitType, List<Expression> arrayDimensions, Expression? elementInit,
    Attributes? attributes = null)
    : base(origin, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(1 <= arrayDimensions.Count);
    ExplicitType = explicitType;
    inferredElementType = explicitType == null ? new InferredTypeProxy() : null;
    ArrayDimensions = arrayDimensions;
    ElementInit = elementInit;
  }

  public AllocateArray(IOrigin origin, Type type, Expression dim, List<Expression> initDisplay,
    Attributes? attributes = null)
    : base(origin, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(initDisplay != null);
    ExplicitType = type;
    inferredElementType = type == null ? new InferredTypeProxy() : null;
    ArrayDimensions = [dim];
    InitDisplay = initDisplay;
  }

  public AllocateArray(Cloner cloner, AllocateArray original)
    : base(cloner, original) {
    ExplicitType = cloner.CloneType(original.ExplicitType);
    // Only an inferred element type has to be carried across; when the user wrote one,
    // ElementType is the ExplicitType just cloned. Without CloneResolvedFields the original proxy
    // would carry a resolution this clone is about to redo, so start from a fresh one.
    inferredElementType = ExplicitType != null ? null
      : cloner.CloneResolvedFields ? cloner.CloneType(original.ElementType) : new InferredTypeProxy();
    if (original.InitDisplay != null) {
      Contract.Assert(original.ArrayDimensions.Count == 1);
      ArrayDimensions = [cloner.CloneExpr(original.ArrayDimensions[0])];
      InitDisplay = original.InitDisplay.ConvertAll(cloner.CloneExpr);
    } else {
      ArrayDimensions = original.ArrayDimensions.Select(cloner.CloneExpr).ToList();
      ElementInit = cloner.CloneExpr(original.ElementInit);
    }

    if (cloner.CloneResolvedFields) {
      Type = cloner.CloneType(original.Type);
    }
  }
  public AllocateArray Clone(Cloner cloner) {
    return new AllocateArray(cloner, this);
  }

  public override bool CanAffectPreviouslyKnownExpressions => false;

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in ArrayDimensions) {
        yield return e;
      }
      if (ElementInit != null) {
        yield return ElementInit;
      }
      if (InitDisplay != null) {
        foreach (var e in InitDisplay) {
          yield return e;
        }
      }
    }
  }

  public override IEnumerable<Statement> SubStatements => [];


  public override IEnumerable<INode> Children {
    get {
      if (!WasResolved) {
        return PreResolveChildren;
      }

      return (ElementType.Nodes ?? []).Concat(SubExpressions).Concat<Node>(SubStatements);
    }
  }

  public override IEnumerable<INode> PreResolveChildren =>
    new[] { ExplicitType, Type }.OfType<Node>()
      .Concat(ArrayDimensions)
      .Concat(ElementInit != null ? new[] { ElementInit } : Enumerable.Empty<Node>())
      .Concat(InitDisplay ?? Enumerable.Empty<Node>());
}