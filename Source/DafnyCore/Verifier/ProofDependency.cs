using JetBrains.Annotations;
using Microsoft.Dafny;
using IToken = Microsoft.Dafny.IToken;
using PODesc = Microsoft.Dafny.ProofObligationDescription;
using ResolutionContext = Microsoft.Boogie.ResolutionContext;

namespace DafnyCore.Verifier;

public abstract class ProofDependency {
  public abstract string Description { get; }

  public abstract RangeToken RangeToken { get; }

  public string LocationString() {
    if (RangeToken?.StartToken is null) {
      return "<no location>";
    }
    var fn = RangeToken.StartToken.filename;
    var sl = RangeToken.StartToken.line;
    var sc = RangeToken.StartToken.col - 1;
    return $"{fn}({sl},{sc})";
  }

  public string RangeString() {
    if (RangeToken?.StartToken is null) {
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
    $"requires clause";

  public RequiresDependency(Expression requires) {
    this.requires = requires;
  }
}

public class EnsuresDependency : ProofDependency {
  private Expression ensures;

  public override RangeToken RangeToken =>
    ensures.RangeToken;

  public override string Description =>
    "ensures clause";

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
    $"requires clause at {requires.RangeString()} from call";

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
    $"ensures clause at {ensures.RangeString()} from call";

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
    $"call";

  public CallDependency(CallStmt call) {
    this.call = call;
  }
}

public class AssumptionDependency : ProofDependency {
  private Expression expr;

  public override RangeToken RangeToken =>
    expr.RangeToken;

  public override string Description =>
    comment ?? $"assume {OriginalString()}";

  private string comment;

  public AssumptionDependency(string comment, Expression expr) {
    this.comment = comment;
    this.expr = expr;
  }
}

public class InvariantDependency : ProofDependency {
  private Expression invariant;

  public override RangeToken RangeToken =>
    invariant.RangeToken;

  public override string Description =>
    $"loop invariant";

  public InvariantDependency(Expression invariant) {
    this.invariant = invariant;
  }
}

public class AssignmentDependency : ProofDependency {
  public override RangeToken RangeToken { get; }

  public override string Description =>
     "assignment (or return)";

  public AssignmentDependency(RangeToken rangeToken) {
    this.RangeToken = rangeToken;
  }
}

public class FunctionDefinitionDependency : ProofDependency {
  public override RangeToken RangeToken => function.RangeToken;

  public override string Description =>
    $"function definition for {function.Name}";

  private Function function;

  public FunctionDefinitionDependency(Function f) {
    function = f;
  }
}