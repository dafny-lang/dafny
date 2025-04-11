#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

public class ActualBindings : NodeWithoutOrigin {
  public List<ActualBinding> ArgumentBindings;

  [SyntaxConstructor]
  public ActualBindings(List<ActualBinding> argumentBindings) {
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
    ArgumentBindings = actuals.ConvertAll(actual => new ActualBinding(null, actual));
  }

  [FilledInDuringResolution]
  private List<Expression>? arguments; // set by ResolveActualParameters during resolution

  public bool WasResolved => arguments != null;

  public List<Expression> Arguments => arguments!;

  public void AcceptArgumentExpressionsAsExactParameterList(List<Expression>? args = null) {
    Contract.Requires(!WasResolved); // this operation should be done at most once
    Contract.Assume(ArgumentBindings.TrueForAll(arg => arg.Actual.WasResolved()));
    arguments = args ?? ArgumentBindings.ConvertAll(binding => binding.Actual);
  }

  public override IEnumerable<INode> Children => arguments == null ? ArgumentBindings : arguments;
  public override IEnumerable<INode> PreResolveChildren => Children;
}

public class ActualBinding : NodeWithoutOrigin {
  public IOrigin? FormalParameterName;
  public Expression Actual;
  public bool IsGhost;

  public override IEnumerable<INode> Children => new List<Node> { Actual }.Where(x => x != null);

  public override IEnumerable<INode> PreResolveChildren => Children;

  [SyntaxConstructor]
  public ActualBinding(IOrigin? formalParameterName, Expression actual, bool isGhost = false) {
    FormalParameterName = formalParameterName;
    Actual = actual;
    IsGhost = isGhost;
  }
}