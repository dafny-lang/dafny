#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// Either ElementInit or InitDisplay will be set
/// </summary>
public class AllocateArray : TypeRhs, ICloneable<AllocateArray> {
  public Type ExplicitType;
  public readonly List<Expression> ArrayDimensions;
  public readonly Expression? ElementInit;
  public readonly List<Expression>? InitDisplay;

  [SyntaxConstructor]
  public AllocateArray(IOrigin origin, Type explicitType, List<Expression> arrayDimensions, Expression elementInit,
    Attributes? attributes = null)
    : base(origin, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(1 <= arrayDimensions.Count);
    ExplicitType = explicitType;
    ArrayDimensions = arrayDimensions;
    ElementInit = elementInit;
  }

  public AllocateArray(IOrigin origin, Type type, Expression dim, List<Expression> initDisplay,
    Attributes? attributes = null)
    : base(origin, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(initDisplay != null);
    ExplicitType = type;
    ArrayDimensions = [dim];
    InitDisplay = initDisplay;
  }

  public AllocateArray(Cloner cloner, AllocateArray original)
    : base(cloner, original) {
    ExplicitType = cloner.CloneType(original.ExplicitType);
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
      if (Type == null) {
        return PreResolveChildren;
      }

      return ExplicitType.Nodes.Concat(SubExpressions).Concat<Node>(SubStatements);
    }
  }

  public override IEnumerable<INode> PreResolveChildren =>
    new[] { ExplicitType, Type }.OfType<Node>()
      .Concat(ArrayDimensions)
      .Concat(ElementInit != null ? new[] { ElementInit } : Enumerable.Empty<Node>())
      .Concat(InitDisplay ?? Enumerable.Empty<Node>());
}