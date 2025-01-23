// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using Microsoft.Dafny;
using PODesc = Microsoft.Dafny.ProofObligationDescription;

namespace DafnyCore.Verifier;

// A proof dependency represents a particular part of a Dafny program
// that may be used in the process of proving its correctness. When
// Boogie proves a particular verification condition, it returns a
// list of strings, returned by the SMT solver, indicating which
// program elements were used in completing the proof. After this, the
// ProofDependencyManager can map each string to a more structured
// ProofDependency.
public abstract class ProofDependency {
  public abstract string Description { get; }

  public abstract IOrigin Range { get; }

  public string LocationString() {
    if (Range?.StartToken is null) {
      return "<no location>";
    }
    var fn = Range.StartToken.filename;
    var sl = Range.StartToken.line;
    var sc = Range.StartToken.col;
    return $"{fn}({sl},{sc})";
  }

  public string RangeString() {
    if (Range?.StartToken is null) {
      return "<no range>";
    }
    var fn = Range.StartToken.filename;
    var sl = Range.StartToken.line;
    var sc = Range.StartToken.col;
    var el = Range.EndToken.line;
    var ec = Range.EndToken.col;
    return $"{fn}({sl},{sc})-({el},{ec})";
  }

  public string OriginalString() {
    return Range?.PrintOriginal();
  }
}

// Represents the portion of a Dafny program corresponding to a proof
// obligation. This is particularly important to track because if a particular
// assertion batch can be proved without proving one of the assertions that is
// a proof obligation within it, that assertion must have been proved vacuously.
public class ProofObligationDependency(Microsoft.Boogie.IToken tok, ProofObligationDescription proofObligation)
  : ProofDependency {
  public override IOrigin Range { get; } = tok as SourceOrigin ?? (proofObligation as AssertStatementDescription)?.AssertStatement.Origin ?? BoogieGenerator.ToDafnyToken(true, tok);

  public ProofObligationDescription ProofObligation { get; } = proofObligation;

  public override string Description =>
      $"{ProofObligation.SuccessDescription}";
}

public class AssumedProofObligationDependency(IOrigin tok, ProofObligationDescription proofObligation)
  : ProofDependency {
  public override IOrigin Range { get; } = tok;

  public ProofObligationDescription ProofObligation { get; } = proofObligation;

  public override string Description =>
      $"assumption that {ProofObligation.SuccessDescription}";
}

// Represents the assumption of a requires clause in the process of
// proving a Dafny definition.
public class RequiresDependency(IOrigin token, Expression requires) : ProofDependency {
  public override IOrigin Range =>
    token as SourceOrigin ?? requires.Origin;

  public override string Description =>
    $"requires clause";
}

// Represents the goal of proving an ensures clause of a Dafny definition.
public class EnsuresDependency(IOrigin token, Expression ensures) : ProofDependency {
  public override IOrigin Range =>
    token as SourceOrigin ?? ensures.Origin;

  public override string Description =>
    "ensures clause";
}

// Represents the goal of proving a specific requires clause of a specific
// call.
public class CallRequiresDependency(CallDependency call, RequiresDependency requires) : ProofDependency {
  public readonly CallDependency call = call;

  public override IOrigin Range =>
    call.Range;

  public override string Description =>
    $"requires clause at {requires.RangeString()} from call";
}

// Represents the assumption of a specific ensures clause of a specific
// call.
public class CallEnsuresDependency(CallDependency call, EnsuresDependency ensures) : ProofDependency {
  public readonly CallDependency call = call;

  public override IOrigin Range =>
    call.Range;

  public override string Description =>
    $"ensures clause at {ensures.RangeString()} from call";
}

// Represents the fact that a particular call occurred.
public class CallDependency(CallStmt call) : ProofDependency {
  public readonly CallStmt call = call;

  public override IOrigin Range =>
    call.Origin;

  public override string Description =>
    $"call";
}

// Represents the assumption of a predicate in an `assume` statement.
public class AssumptionDependency(bool warnWhenUnused, string comment, Expression expr) : ProofDependency {
  public override IOrigin Range =>
    Expr.Origin;

  public override string Description =>
    comment ?? OriginalString();

  public bool WarnWhenUnused { get; } = warnWhenUnused;

  public Expression Expr { get; } = expr;
}

// Represents the invariant of a loop.
public class InvariantDependency(Expression invariant) : ProofDependency {
  public override IOrigin Range =>
    invariant.Origin;

  public override string Description =>
    $"loop invariant";
}

// Represents an assignment statement. This includes the assignment to an
// out parameter implicit in a return statement.
public class AssignmentDependency(IOrigin rangeOrigin) : ProofDependency {
  public override IOrigin Range { get; } = rangeOrigin;

  public override string Description =>
     "assignment (or return)";
}

// Represents dependency of a proof on the definition of a specific function.
public class FunctionDefinitionDependency(Function f) : ProofDependency {
  public override IOrigin Range => function.Origin;

  public override string Description =>
    $"function definition for {function.Name}";

  public Function function = f;
}