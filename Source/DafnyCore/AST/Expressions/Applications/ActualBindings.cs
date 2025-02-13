#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

public class ActualBindings : NodeWithComputedRange {
  public readonly List<ActualBinding> ArgumentBindings;

  [ParseConstructor]
  public ActualBindings(IOrigin origin, List<ActualBinding> argumentBindings) : base(origin)
  {
    ArgumentBindings = argumentBindings;
  }

  public ActualBindings(List<ActualBinding> argumentBindings) {
    Contract.Requires(argumentBindings != null);
    ArgumentBindings = argumentBindings;
  }

  public ActualBindings(Cloner cloner, ActualBindings original) {
    ArgumentBindings = original.ArgumentBindings.Select(actualBinding => new ActualBinding(
      actualBinding.FormalParameterName == null ? null : cloner.Origin((IOrigin)actualBinding.FormalParameterName),
      cloner.CloneExpr(actualBinding.Actual))).ToList();
    if (cloner.CloneResolvedFields) {
      arguments = original.Arguments?.Select(cloner.CloneExpr).ToList();
    }
  }

  public ActualBindings(List<Expression> actuals) {
    Contract.Requires(actuals != null);
    ArgumentBindings = actuals.ConvertAll(actual => new ActualBinding(null, actual));
  }

  [FilledInDuringResolution]
  private List<Expression> arguments; // set by ResolveActualParameters during resolution

  public bool WasResolved => arguments != null;

  public List<Expression> Arguments => arguments;

  public void AcceptArgumentExpressionsAsExactParameterList(List<Expression> args = null) {
    Contract.Requires(!WasResolved); // this operation should be done at most once
    Contract.Assume(ArgumentBindings.TrueForAll(arg => arg.Actual.WasResolved()));
    arguments = args ?? ArgumentBindings.ConvertAll(binding => binding.Actual);
  }

  public override IEnumerable<INode> Children => arguments == null ? ArgumentBindings : arguments;
  public override IEnumerable<INode> PreResolveChildren => Children;
}

public class ActualBinding : NodeWithComputedRange {
  public readonly IOrigin? FormalParameterName;
  public readonly Expression Actual;
  public readonly bool IsGhost;

  public override IEnumerable<INode> Children => new List<Node> { Actual }.Where(x => x != null);

  public override IEnumerable<INode> PreResolveChildren => Children;

  [ParseConstructor]
  public ActualBinding(IOrigin origin, IOrigin? formalParameterName, Expression actual, bool isGhost = false) : base(origin) {
    FormalParameterName = formalParameterName;
    Actual = actual;
    IsGhost = isGhost;
  }

  public ActualBinding(IOrigin? formalParameterName, Expression actual, bool isGhost = false) {
    FormalParameterName = formalParameterName;
    Actual = actual;
    IsGhost = isGhost;
  }
}