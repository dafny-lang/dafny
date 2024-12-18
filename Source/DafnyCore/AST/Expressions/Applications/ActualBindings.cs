using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class ActualBindings : TokenNode {
  public readonly List<ActualBinding> ArgumentBindings;

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

public class ActualBinding : TokenNode {
  public readonly IOrigin /*?*/ FormalParameterName;
  public readonly Expression Actual;
  public readonly bool IsGhost;

  public override IEnumerable<INode> Children => new List<Node> { Actual }.Where(x => x != null);

  public override IEnumerable<INode> PreResolveChildren => Children;

  public ActualBinding(IOrigin /*?*/ formalParameterName, Expression actual, bool isGhost = false) {
    Contract.Requires(actual != null);
    FormalParameterName = formalParameterName;
    Actual = actual;
    IsGhost = isGhost;
  }
}