using System;
using JetBrains.Annotations;
using Microsoft.Boogie;
using Microsoft.Dafny;
using IToken = Microsoft.Dafny.IToken;
using PODesc = Microsoft.Dafny.ProofObligationDescription;

namespace DafnyCore.Verifier;

public abstract class ProofDependency {
  public abstract string Description { get; }

  public abstract RangeToken RangeToken { get; }

  public string LocationString() {
    return RangeToken?.StartToken is null
      ? "<no location>"
      : $"{RangeToken.StartToken.filename}({RangeToken.StartToken.line},{RangeToken.StartToken.col - 1})";
  }

  public string RangeString() {
    if (RangeToken is null) {
      return "<no range>";
    }
    var fn = RangeToken.StartToken.filename;
    var sl = RangeToken.StartToken.line;
    var sc = RangeToken.StartToken.col - 1;
    var el = RangeToken.EndToken.line;
    var ec = RangeToken.EndToken.col - 1;
    return $"{fn}({sl},{sc})-({el},{ec})";
  }

  public string OriginalString() {
    return RangeToken?.PrintOriginal();
  }
}

public class ProofObligationDependency : ProofDependency {
  public override RangeToken RangeToken { get; }

  public PODesc.ProofObligationDescription ProofObligation { get; }

  public override string Description =>
      $"{ProofObligation.SuccessDescription}";

  public ProofObligationDependency(IToken tok, PODesc.ProofObligationDescription proofObligation) {
    RangeToken = tok as RangeToken ?? new RangeToken(tok, tok);
    ProofObligation = proofObligation;
  }
}

public class RequiresDependency : ProofDependency {
  private Expression requires;

  public override RangeToken RangeToken =>
    requires.RangeToken;

  public override string Description =>
    $"requires {requires.RangeToken.PrintOriginal()}";

  public RequiresDependency(Expression requires) {
    this.requires = requires;
  }
}

public class EnsuresDependency : ProofDependency {
  private Expression ensures;

  public override RangeToken RangeToken =>
    ensures.RangeToken;

  public override string Description =>
    $"ensures {ensures.RangeToken.PrintOriginal()}";

  public EnsuresDependency(Expression ensures) {
    this.ensures = ensures;
  }
}

public class CallRequiresDependency : ProofDependency {
  private CallDependency call;
  private RequiresDependency requires;

  public override RangeToken RangeToken =>
    call.RangeToken;

  public override string Description =>
    $"{requires.Description} from call at {call.Description}";

  public CallRequiresDependency(CallDependency call, RequiresDependency requires) {
    this.call = call;
    this.requires = requires;
  }
}

public class CallEnsuresDependency : ProofDependency {
  private CallDependency call;
  private EnsuresDependency ensures;

  public override RangeToken RangeToken =>
    call.RangeToken;

  public override string Description =>
    $"{ensures.Description} from call at {call.Description}";

  public CallEnsuresDependency(CallDependency call, EnsuresDependency ensures) {
    this.call = call;
    this.ensures = ensures;
  }
}

public class CallDependency : ProofDependency {
  private CallStmt call;

  public override RangeToken RangeToken =>
    call.RangeToken;

  public override string Description =>
    $"{LocationString()}: {OriginalString()};";

  public CallDependency(CallStmt call) {
    this.call = call;
  }
}

public class AssertionDependency : ProofDependency {
  private Expression expr;

  public override RangeToken RangeToken =>
    expr.RangeToken;

  public override string Description =>
    $"assert {OriginalString()};";

  public AssertionDependency(Expression expr) {
    this.expr = expr;
  }
}

public class AssumptionDependency : ProofDependency {
  private Expression expr;

  public override RangeToken RangeToken =>
    expr.RangeToken;

  public override string Description =>
      $"assume {OriginalString()}";

  public AssumptionDependency(Expression expr) {
    this.expr = expr;
  }
}

public class InvariantDependency : ProofDependency {
  private Expression invariant;

  public override RangeToken RangeToken =>
    invariant.RangeToken;

  public override string Description =>
    $"invariant {invariant.RangeToken.PrintOriginal()}";

  public InvariantDependency(Expression invariant) {
    this.invariant = invariant;
  }
}

public class AssignmentDependency : ProofDependency {
  public override RangeToken RangeToken { get; }

  public override string Description => "assignment";

  public AssignmentDependency(RangeToken rangeToken) {
    this.RangeToken = rangeToken;
  }
}

public class InternalDependency : ProofDependency {
  public override RangeToken RangeToken => null;
  public override string Description { get; }

  public InternalDependency(string description) {
    Description = description;
  }
}

// Temporary placeholder. Remove when all creation sites use a different
// implementation.
public class NodeOnlyDependency : ProofDependency {
  public override RangeToken RangeToken { get; }

  public override string Description =>
    $"{LocationString()}: {OriginalString()}";

  public NodeOnlyDependency([NotNull] Node node) {
    RangeToken = node.RangeToken;
  }
}
