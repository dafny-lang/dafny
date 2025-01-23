using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Linq.Expressions;
using System.Text;
using JetBrains.Annotations;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public abstract class ProofObligationDescription : Boogie.ProofObligationDescription {
  public virtual bool IsImplicit => true;

  // An expression that, if verified, would trigger a success for this ProofObligationDescription
  // It is only printed for the user, so it does not need to be resolved.
  public virtual Expression GetAssertedExpr(DafnyOptions options) {
    return null;
  }

  // Substituting replaces the token of a substituting expression by the token of the identifierExpr being susbstituted,
  // Since the printer requires the token of IdentifierExpr to be Token.NoToken to print the custom name in Dafny mode,
  // we just wrap the identifierExpr into a ParensExpression, as it is the case for any other expression.
  protected static Expression ToSubstitutableExpression(BoundVar bvar) {
    var expression = new IdentifierExpr(bvar.Origin, bvar);
    return new ParensExpression(bvar.Origin, expression) { Type = bvar.Type, ResolvedExpression = expression };
  }

  // Returns a list of primed copies of the given `BoundVar`s.
  protected static List<BoundVar> MakePrimedBoundVars(List<BoundVar> bvars) {
    return bvars.Select(bvar => new BoundVar(Token.NoToken, bvar.Name + "'", bvar.Type)).ToList();
  }

  // Returns a substitution map from each given `BoundVar`s to a substitutable expression of a primed copy of the var.
  protected static Dictionary<IVariable, Expression> MakePrimedBoundVarSubstMap(List<BoundVar> bvars, out List<BoundVar> primedVars, out List<Expression> primedExprs) {
    primedVars = MakePrimedBoundVars(bvars);
    primedExprs = primedVars.Select(ToSubstitutableExpression).ToList();
    return bvars.Zip(primedExprs).ToDictionary(item => item.Item1 as IVariable, item => item.Item2);
  }

  // Creates primed copies of the given `BoundVar`s along with a Substituter for substituting the primed vars,
  // and also returns a combined quantifier range of the form
  //
  //   range && range[i0 := i0', i1 := i1', ...] && (i0 != i0' || i1 != i1' || ...)
  //
  // Made for use in comparing expressions across loop iterations / quantified bodies.
  protected static void MakePrimedBoundVarsAndRange(List<BoundVar> bvars, Expression range,
    out List<BoundVar> primedVars, out Substituter sub, out Expression combinedRange) {
    var substMap = MakePrimedBoundVarSubstMap(bvars, out primedVars, out _);
    sub = new Substituter(null, substMap, new());

    var rangeAndRangePrime = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, range, sub.Substitute(range));
    var indicesDistinct = bvars
      .Select(var =>
        new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Neq, ToSubstitutableExpression(var), substMap[var]))
      .Aggregate((acc, disjunct) =>
        new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Or, acc, disjunct));
    combinedRange = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, rangeAndRangePrime, indicesDistinct);
  }

  public virtual bool ProvedOutsideUserCode => false;

  public virtual string GetExtraExplanation() {
    return null;
  }
}

//// Arithmetic and logical operators, conversions

public class DivisorNonZero(Expression divisor) : ProofObligationDescription {
  public override string SuccessDescription =>
    "divisor is always non-zero.";

  public override string FailureDescription =>
    "possible division by zero";

  public override string ShortDescription => "non-zero divisor";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new BinaryExpr(divisor.Origin, BinaryExpr.Opcode.Neq, divisor, new LiteralExpr(divisor.Origin, 0));
  }
}

public abstract class ShiftOrRotateBound(bool shift, Expression amount) : ProofObligationDescription {
  protected readonly string shiftOrRotate = shift ? "shift" : "rotate";
  protected readonly Expression amount = amount;
}

public class ShiftLowerBound(bool shift, Expression amount) : ShiftOrRotateBound(shift, amount) {
  public override string SuccessDescription =>
    $"{shiftOrRotate} amount is always non-negative";

  public override string FailureDescription =>
    $"{shiftOrRotate} amount must be non-negative";

  public override string ShortDescription => $"{shiftOrRotate} lower bound";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new BinaryExpr(amount.Origin, BinaryExpr.Opcode.Le, Expression.CreateIntLiteral(amount.Origin, 0), amount);
  }
}

public class ShiftUpperBound(int width, bool shift, Expression amount) : ShiftOrRotateBound(shift, amount) {
  public override string SuccessDescription =>
    $"{shiftOrRotate} amount is always within the width of the result ({width})";

  public override string FailureDescription =>
    $"{shiftOrRotate} amount must not exceed the width of the result ({width})";

  public override string ShortDescription => $"{shiftOrRotate} upper bound";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new BinaryExpr(amount.Origin, BinaryExpr.Opcode.Le, amount, Expression.CreateIntLiteral(amount.Origin, width));
  }
}

public class ConversionIsNatural(string prefix, Expression value) : ProofObligationDescription {
  public override string SuccessDescription =>
    $"{prefix}value to be converted is always a natural number";

  public override string FailureDescription =>
    $"{prefix}value to be converted might be bigger than every natural number";

  public override string ShortDescription => "converted value is natural";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new TypeTestExpr(value.Origin, value, Type.Nat());
  }
}

public class ConversionSatisfiesConstraints(string prefix, string kind, string name, Expression constraint)
  : ProofObligationDescription {
  public override string SuccessDescription =>
    $"{prefix}result of operation never violates {kind} constraints for '{name}'";

  public override string FailureDescription =>
    $"{prefix}result of operation might violate {kind} constraint for '{name}'";

  public override string ShortDescription => "conversion satisfies type constraints";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return constraint;
  }
}

public class OrdinalSubtractionIsNatural(Expression rhs) : ProofObligationDescription {
  public override string SuccessDescription =>
    "RHS of ORDINAL subtraction is always a natural number";

  public override string FailureDescription =>
    "RHS of ORDINAL subtraction must be a natural number, but the given RHS might be larger";

  public override string ShortDescription => "ordinal subtraction is natural";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new ExprDotName(rhs.Origin, rhs, new Name("IsNat"), null);
  }
}

public class OrdinalSubtractionUnderflow(Expression lhs, Expression rhs) : ProofObligationDescription {
  public override string SuccessDescription =>
    "ORDINAL subtraction will never go below limit ordinal";

  public override string FailureDescription =>
    "ORDINAL subtraction might underflow a limit ordinal (that is, RHS might be too large)";

  public override string ShortDescription => "ordinal subtraction underflow";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new BinaryExpr(
      rhs.Origin,
      BinaryExpr.Opcode.Le,
      new ExprDotName(rhs.Origin, rhs, new Name("Offset"), null),
      new ExprDotName(lhs.Origin, lhs, new Name("Offset"), null)
    );
  }
}

public class CharOverflow(Expression e0, Expression e1) : ProofObligationDescription {
  public override string SuccessDescription =>
    "char addition will not overflow";

  public override string FailureDescription =>
    "char addition might overflow";

  public override string ShortDescription => "char overflow";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    var sum = new BinaryExpr(
      e0.Origin,
      BinaryExpr.Opcode.Add,
      new ConversionExpr(e0.Origin, e0, Type.Int),
      new ConversionExpr(e1.Origin, e1, Type.Int)
    );
    return Utils.MakeCharBoundsCheck(options, sum);
  }
}

public class CharUnderflow(Expression e0, Expression e1) : ProofObligationDescription {
  public override string SuccessDescription =>
    "char subtraction will not underflow";

  public override string FailureDescription =>
    "char subtraction might underflow";

  public override string ShortDescription => "char underflow";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    var diff = new BinaryExpr(
      e0.Origin,
      BinaryExpr.Opcode.Sub,
      new ConversionExpr(e0.Origin, e0, Type.Int),
      new ConversionExpr(e1.Origin, e1, Type.Int)
    );
    return Utils.MakeCharBoundsCheck(options, diff);
  }
}

public class ConversionFit(string what, Type toType, Expression boundsCheck, string prefix = "")
  : ProofObligationDescription {
  public override string SuccessDescription =>
    $"{prefix}{what} to be converted will always fit in {toType}";

  public override string FailureDescription =>
    $"{prefix}{what} to be converted might not fit in {toType}";

  public override string ShortDescription => "conversion fit";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return boundsCheck;
  }
}

public class NonNegative(string what, Expression expr) : ProofObligationDescription {
  public override string SuccessDescription =>
    $"{what} is never negative";

  public override string FailureDescription =>
    $"{what} might be negative";

  public override string ShortDescription => "non-negative";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new BinaryExpr(
      expr.Origin,
      BinaryExpr.Opcode.Le,
      Expression.CreateIntLiteral(expr.Origin, 0),
      expr
    );
  }
}

public class ConversionPositive(string what, Type toType, Expression expr, string prefix = "")
  : ProofObligationDescription {
  public override string SuccessDescription =>
    $"{prefix}{what} is always positive";

  public override string FailureDescription =>
    $"{prefix}a negative {what} cannot be converted to an {toType}";

  public override string ShortDescription => "conversion positive";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new BinaryExpr(
      expr.Origin,
      BinaryExpr.Opcode.Le,
      Expression.CreateIntLiteral(expr.Origin, 0),
      expr
    );
  }
}

public class IsInteger(Expression expr, string prefix = "") : ProofObligationDescription {
  public override string SuccessDescription =>
    $"{prefix}the real-based number is an integer";

  public override string FailureDescription =>
    $"{prefix}the real-based number must be an integer (if you want truncation, apply .Floor to the real-based number)";

  public override string ShortDescription => "is integer";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new BinaryExpr(
      expr.Origin,
      BinaryExpr.Opcode.Eq,
      expr,
      new ConversionExpr(expr.Origin, new ExprDotName(expr.Origin, expr, new Name("Floor"), null), Type.Real)
    );
  }
}

//// Object properties

public class NonNull(string what, Expression expr, bool plural = false) : ProofObligationDescription {
  public override string SuccessDescription =>
    $"{PluralSuccess}{what} is never null";

  public override string FailureDescription =>
    $"{PluralFailure}{what} might be null";

  public override string ShortDescription => $"{what} non-null";
  private string PluralSuccess => plural ? "each " : "";
  private string PluralFailure => plural ? "some " : "";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new BinaryExpr(expr.Origin, BinaryExpr.Opcode.Neq, expr, new LiteralExpr(expr.Origin));
  }
}

public class IsAllocated(
  string what,
  string when,
  Expression expr,
  [CanBeNull] Label atLabel = null,
  bool plural = false)
  : ProofObligationDescription {
  public override string SuccessDescription =>
    $"{PluralSuccess}{what} is always allocated{WhenSuffix}";

  public override string FailureDescription =>
    $"{PluralFailure}{what} could not be proved to be allocated{WhenSuffix}";

  public override string ShortDescription => $"{what} allocated";

  [CanBeNull] private readonly string when = when;
  private string WhenSuffix => when is null ? "" : $" {when}";
  private string PluralSuccess => plural ? "each " : "";
  private string PluralFailure => plural ? "some " : "";

  public static string HelperFormal(Formal formal) {
    return $" -- if you add 'new' before the parameter declaration, like 'new {formal.Name}: {formal.Type.ToString()}',"
           + " arguments can refer to expressions possibly unallocated in the previous state";
  }

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new OldExpr(expr.Origin, new UnaryOpExpr(expr.Origin, UnaryOpExpr.Opcode.Allocated, expr), atLabel?.Name);
  }
}

public class IsOlderProofObligation : ProofObligationDescription {
  public override string SuccessDescription {
    get {
      var successOlder = olderParameterCount == 1 ? " is" : "s are";
      var successOther = otherParameterCount == 1 ? "the" : "any";
      return $"the 'older' parameter{successOlder} not newer than {successOther} other parameter when the predicate returns 'true'";
    }
  }

  public override string FailureDescription {
    get {
      var failureOlder = olderParameterCount == 1 ? "the" : "an";
      var failureOther =
        olderParameterCount == 1 && otherParameterCount == 1 ? "the other parameter" :
        otherParameterCount == 1 ? "the non-'older' parameter" :
        "all non-'older' parameters";
      return $"{failureOlder} 'older' parameter might be newer than {failureOther} when the predicate returns 'true'";
    }
  }

  public override string ShortDescription => $"older parameter{(2 <= olderParameterCount ? "s" : "")}";

  private readonly int olderParameterCount;
  private readonly int otherParameterCount;

  public IsOlderProofObligation(int olderParameterCount, int allParameterCount) {
    Contract.Requires(1 <= olderParameterCount);
    Contract.Requires(olderParameterCount <= allParameterCount);
    this.olderParameterCount = olderParameterCount;
    this.otherParameterCount = allParameterCount - olderParameterCount;
  }
}

//// Contract constraints

public abstract class ProofObligationDescriptionCustomMessages(
  [CanBeNull] string customErrMsg,
  [CanBeNull] string customSuccessMsg)
  : ProofObligationDescription {
  protected readonly string customErrMsg = customErrMsg;
  private readonly string customSuccessMsg = customSuccessMsg;

  public override string SuccessDescription =>
    customSuccessMsg ?? DefaultSuccessDescription;

  public abstract string DefaultSuccessDescription { get; }
  public override string FailureDescription =>
    customErrMsg ?? DefaultFailureDescription;
  public abstract string DefaultFailureDescription { get; }
}

public class PreconditionSatisfied(
  Expression expr,
  [CanBeNull] string customErrMsg,
  [CanBeNull] string customSuccessMsg)
  : ProofObligationDescriptionCustomMessages(customErrMsg, customSuccessMsg) {
  public override string DefaultSuccessDescription =>
    "function precondition satisfied";

  public override string DefaultFailureDescription =>
    "function precondition could not be proved";

  public override string ShortDescription => "precondition";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return expr;
  }
}

public class AssertStatementDescription(
  PredicateStmt assertStmt,
  [CanBeNull] string customErrMsg,
  [CanBeNull] string customSuccessMsg)
  : ProofObligationDescriptionCustomMessages(customErrMsg, customSuccessMsg) {
  public override string DefaultSuccessDescription =>
    "assertion always holds";

  public override string DefaultFailureDescription =>
    "assertion might not hold";

  public override string ShortDescription => "assert statement";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return AssertStatement.Expr;
  }

  public PredicateStmt AssertStatement { get; } = assertStmt;

  // We provide a way to mark an assertion as an intentional element of a
  // proof by contradiction with the `{:contradiction}` attribute. Dafny
  // skips warning about such assertions being proved due to contradictory
  // assumptions.
  public bool IsIntentionalContradiction => Attributes.Contains(AssertStatement.Attributes, "contradiction");

  public override bool IsImplicit => false;
}

// The Boogie version does not support custom error messages yet
public class RequiresDescription(Expression expr, [CanBeNull] string customErrMsg, [CanBeNull] string customSuccessMsg)
  : ProofObligationDescriptionCustomMessages(customErrMsg, customSuccessMsg) {
  public override string DefaultSuccessDescription =>
    "the precondition always holds";

  public override string DefaultFailureDescription =>
    "this is the precondition that could not be proved";

  public override string ShortDescription => "requires";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return expr;
  }
}

// The Boogie version does not support custom error messages yet
public class EnsuresDescription(Expression expr, [CanBeNull] string customErrMsg, [CanBeNull] string customSuccessMsg)
  : ProofObligationDescriptionCustomMessages(customErrMsg, customSuccessMsg) {
  public override string DefaultSuccessDescription =>
    "this postcondition holds";

  public override string DefaultFailureDescription =>
    "this is the postcondition that could not be proved";

  // Same as FailureDescription but used not as a "related" error, but as an error by itself
  public string FailureDescriptionSingle =>
    customErrMsg ?? "this postcondition could not be proved on a return path";

  public string FailureAtPathDescription =>
    customErrMsg ?? new PostconditionDescription().FailureDescription;

  public override string ShortDescription => "ensures";

  public override bool IsImplicit => false;

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return expr;
  }
}

public class LoopInvariant(Expression expr, [CanBeNull] string customErrMsg, [CanBeNull] string customSuccessMsg)
  : ProofObligationDescriptionCustomMessages(customErrMsg, customSuccessMsg) {
  public override string DefaultSuccessDescription =>
"loop invariant always holds";

  public override string DefaultFailureDescription =>
    "loop invariant violation";

  public override string ShortDescription => "loop invariant";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return expr;
  }
}

public class CalculationStep(Expression expr, BlockStmt hints) : ProofObligationDescription {
  public override string SuccessDescription =>
    "the calculation step between the previous line and this line always holds";

  public override string FailureDescription =>
    "the calculation step between the previous line and this line could not be proved";

  public override string ShortDescription => "calc step";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return expr;
  }

  public override string GetExtraExplanation() {
    if (hints is null || hints.Body is null || hints.Body.Count == 0) {
      return null;
    }

    StringBuilder builder = new();
    builder.Append("\n  asserted after the following statements:");

    // These can be deeply nested for some reason
    List<Statement> stmts = hints.Body;
    while (stmts.Count == 1 && stmts[0] is BlockStmt bs) {
      stmts = bs.Body;
    }

    foreach (var stmt in stmts) {
      builder.Append($"\n    {stmt}");
    }

    return builder.ToString();
  }
}

public class EnsuresStronger(Expression expr) : ProofObligationDescription {
  public override string SuccessDescription =>
    "the method provides a postcondition equal to or more detailed than in its parent trait";

  public override string FailureDescription =>
    "the method must provide an equal or more detailed postcondition than in its parent trait";

  public override string ShortDescription => "ensures stronger";

  public override bool ProvedOutsideUserCode => true;

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return expr;
  }
}

public class RequiresWeaker(Expression expr) : ProofObligationDescription {
  public override string SuccessDescription =>
    "the method provides a precondition equal to or more permissive than in its parent trait";

  public override string FailureDescription =>
    "the method must provide an equal or more permissive precondition than in its parent trait";

  public override string ShortDescription => "requires weaker";

  public override bool ProvedOutsideUserCode => true;

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return expr;
  }
}

public class ForallPostcondition(Expression expr) : ProofObligationDescription {
  public override string SuccessDescription =>
    "postcondition of forall statement always holds";

  public override string FailureDescription =>
    "possible violation of postcondition of forall statement";

  public override string ShortDescription => "forall ensures";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return expr;
  }
}

public class YieldEnsures(Expression expr) : ProofObligationDescription {
  public override string SuccessDescription =>
    "yield-ensures condition always holds";

  public override string FailureDescription =>
    "possible violation of yield-ensures condition";

  public override string ShortDescription => "yield ensures";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return expr;
  }
}

public class TraitFrame(
  string whatKind,
  bool isModify,
  List<FrameExpression> subsetFrames,
  List<FrameExpression> supersetFrames)
  : ProofObligationDescription {
  public override string SuccessDescription =>
    isModify
      ? $"{whatKind} abides by trait context's modifies clause"
      : $"{whatKind} abides by trait context's reads clause";

  public override string FailureDescription =>
    isModify
      ? $"{whatKind} might modify an object not in the parent trait context's modifies clause"
      : $"{whatKind} might read an object not in the parent trait context's reads clause";

  public override string ShortDescription =>
    isModify ? "trait modifies" : "trait reads";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return Utils.MakeDafnyMultiFrameCheck(supersetFrames, subsetFrames);
  }
}

public class TraitDecreases(string whatKind, Expression expr) : ProofObligationDescription {
  public override string SuccessDescription =>
    $"{whatKind}'s decreases clause is below or equal to that in the trait";

  public override string FailureDescription =>
    $"{whatKind}'s (possibly automatically generated) decreases clause must be below or equal to that in the trait";

  public override string ShortDescription => "trait decreases";

  public override bool ProvedOutsideUserCode => true;

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return expr;
  }
}

public class ReadFrameSubset(
  string whatKind,
  Expression assertedExpr,
  Expression readExpression = null,
  [CanBeNull] IFrameScope scope = null)
  : ProofObligationDescription {
  public override string SuccessDescription =>
    $"sufficient reads clause to {whatKind}";

  public override string FailureDescription =>
    $"insufficient reads clause to {whatKind}" + ExtendedFailureHint();

  public string ExtendedFailureHint() {
    if (readExpression is null) {
      return "";
    }
    if (scope is { Designator: var designator }) {
      var lambdaScope = scope as LambdaExpr;
      var extraHint = "";
      var obj = "object";
      if (readExpression is MemberSelectExpr e) {
        obj = Printer.ExprToString(DafnyOptions.DefaultImmutableOptions, e.Obj, new PrintFlags(UseOriginalDafnyNames: true));
      } else if (readExpression is SeqSelectExpr s) {
        obj = Printer.ExprToString(DafnyOptions.DefaultImmutableOptions, s.Seq, new PrintFlags(UseOriginalDafnyNames: true));
      } else if (readExpression is MultiSelectExpr m) {
        obj = Printer.ExprToString(DafnyOptions.DefaultImmutableOptions, m.Array,
          new PrintFlags(UseOriginalDafnyNames: true));
      }

      if (scope is Function { CoClusterTarget: var x } && x != Function.CoCallClusterInvolvement.None) {
      } else {
        if (lambdaScope == null && readExpression is MemberSelectExpr { MemberName: var field }) {
          extraHint = $" or 'reads {obj}`{field}'";
        }
        var hint = $"adding 'reads {obj}'{extraHint} in the enclosing {designator} specification for resolution";
        if (lambdaScope != null && lambdaScope.Reads.Expressions.Count == 0) {
          hint = $"extracting {readExpression} to a local variable before the lambda expression, or {hint}";
        }

        return $"; Consider {hint}";
      }
    }

    string whyNotWhat = "Memory locations";

    if (whatKind == "read field") {
      whyNotWhat = "Mutable fields";
    } else if (whatKind is "read array element" or "read the indicated range of array elements") {
      whyNotWhat = "Array elements";
    }
    return $"; {whyNotWhat} cannot be accessed within certain scopes, such as default values, the right-hand side of constants, or co-recursive calls";

  }

  public override string ShortDescription => "read frame subset";

  public ReadFrameSubset(string whatKind, FrameExpression subsetFrame, List<FrameExpression> supersetFrames, Expression readExpression = null, [CanBeNull] IFrameScope scope = null)
    : this(whatKind, [subsetFrame], supersetFrames, readExpression, scope) { }

  public ReadFrameSubset(string whatKind, List<FrameExpression> subsetFrames, List<FrameExpression> supersetFrames, Expression readExpression = null, [CanBeNull] IFrameScope scope = null)
    : this(whatKind, Utils.MakeDafnyMultiFrameCheck(supersetFrames, subsetFrames), readExpression, scope) { }

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return assertedExpr;
  }
}

public class ModifyFrameSubset(
  string whatKind,
  List<FrameExpression> subsetFrames,
  List<FrameExpression> supersetFrames)
  : ProofObligationDescription {
  public override string SuccessDescription =>
      $"{whatKind} is allowed by context's modifies clause";

  public override string FailureDescription =>
      $"{whatKind} might violate context's modifies clause";

  public override string ShortDescription => "modify frame subset";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return Utils.MakeDafnyMultiFrameCheck(supersetFrames, subsetFrames);
  }
}

public class FrameDereferenceNonNull(Expression expr) : ProofObligationDescription {
  public override string SuccessDescription =>
    "frame expression does not dereference null";

  public override string FailureDescription =>
    "frame expression might dereference null";

  public override string ShortDescription => "frame dereference";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Neq, expr, new LiteralExpr(Token.NoToken));
  }
}

public class Terminates(
  bool inferredDescreases,
  List<VarDeclStmt> prevGhostLocals,
  Expression allowance,
  List<Expression> oldExpressions,
  List<Expression> newExpressions,
  bool allowNoChange,
  string hint = null)
  : ProofObligationDescription {
  public override string SuccessDescription =>
    "loop or recursion terminates";

  public override string FailureDescription =>
    (inferredDescreases
      ? ("cannot prove termination; try supplying a decreases clause" + (isLoop ? " for the loop" : ""))
      : $"decreases {FormDescription} might not decrease") +
    (hint is null ? "" : $" ({hint})");

  public override string ShortDescription => "termination";

  private bool isLoop => prevGhostLocals is not null;
  private string FormDescription => isLoop ? "expression" : "clause";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    Expression expr = new DecreasesToExpr(Token.NoToken, oldExpressions, newExpressions, allowNoChange);
    if (allowance is not null) {
      expr = Expression.CreateOr(allowance, expr);
    }
    return expr;
  }

  public override string GetExtraExplanation() {
    var builder = new StringBuilder();
    if (prevGhostLocals is not null) {
      builder.Append("\n  with the label `LoopEntry` applied to the loop");
      if (prevGhostLocals.Count > 0) {
        builder.Append("\n  and with the following declarations at the beginning of the loop body:");
        foreach (var decl in prevGhostLocals) {
          builder.Append($"\n    {decl}");
        }
      }

      return builder.ToString();
    }

    return null;
  }
}

public class DecreasesBoundedBelow(
  int N,
  int k,
  string zeroStr,
  List<VarDeclStmt> prevGhostLocals,
  Expression bound,
  string suffix)
  : ProofObligationDescription {
  public override string SuccessDescription =>
    $"decreases {component} is bounded below by {zeroStr}";

  public override string FailureDescription =>
    $"decreases {component} must be bounded below by {zeroStr}{suffix}";

  public override string ShortDescription => "bounded decreases expression";

  public override bool ProvedOutsideUserCode => true;

  private string component => N == 1 ? "expression" : $"expression at index {k}";

  public override Expression GetAssertedExpr(DafnyOptions _) {
    return bound;
  }

  public override string GetExtraExplanation() {
    var builder = new StringBuilder();
    if (prevGhostLocals is not null) {
      builder.Append("\n  with the label `LoopEntry` applied to the loop");
      if (prevGhostLocals.Count > 0) {
        builder.Append("\n  and with the following declarations at the beginning of the loop body:");
        foreach (var decl in prevGhostLocals) {
          builder.Append($"\n    {decl}");
        }
      }

      return builder.ToString();
    }

    return null;
  }
}

public class Modifiable(string description, List<FrameExpression> frames, Expression obj, Field field)
  : ProofObligationDescription {
  public override string SuccessDescription =>
    $"{description} is in the enclosing context's modifies clause";

  public override string FailureDescription =>
    $"assignment might update {description} not in the enclosing context's modifies clause";

  public override string ShortDescription => "modifiable";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return Utils.MakeDafnyFrameCheck(frames, obj, field);
  }
}

public class FunctionContractOverride(bool isEnsures, Expression expr) : ProofObligationDescription {
  public override string SuccessDescription =>
    $"the function provides an equal or {RestrictionDesc} than in its parent trait";

  public override string FailureDescription =>
    $"the function must provide an equal or {RestrictionDesc} than in its parent trait";

  public override string ShortDescription => "contract override valid";

  public override bool ProvedOutsideUserCode => true;

  private string RestrictionDesc =>
    isEnsures ? "more detailed postcondition" : "more permissive precondition";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return expr;
  }
}

//// Structural constraints

public class MatchIsComplete(string matchForm, string missing) : ProofObligationDescription {
  public override string SuccessDescription =>
    $"match {matchForm} covers all cases";

  public override string FailureDescription =>
    $"missing case in match {matchForm}: {missing}";

  public override string ShortDescription => "match complete";

  public override bool ProvedOutsideUserCode => true;

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new LiteralExpr(Token.NoToken, false);
  }

  // ReSharper disable once UnusedMember.Global
  public override string GetExtraExplanation() {
    return (
      "\n  in an added catch-all case:"
      + "\n    case _ => ..."
    );
  }
}

public class AlternativeIsComplete : ProofObligationDescription {
  public override string SuccessDescription =>
    $"alternative cases cover all possibilities";

  public override string FailureDescription =>
    $"alternative cases fail to cover all possibilities";

  public override string ShortDescription => "alternative complete";

  public override bool ProvedOutsideUserCode => true;

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new LiteralExpr(Token.NoToken, false);
  }

  // ReSharper disable once UnusedMember.Global
  public override string GetExtraExplanation() {
    return (
      "\n  in an added catch-all case:"
      + "\n    case true => ..."
    );
  }
}

public class PatternShapeIsValid(Expression expr, string ctorName) : ProofObligationDescription {
  public override string SuccessDescription =>
    $"RHS will always match the pattern '{ctorName}'";

  public override string FailureDescription =>
    $"RHS is not certain to look like the pattern '{ctorName}'";

  public override string ShortDescription => "pattern shape valid";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new ExprDotName(Token.NoToken, expr, new Name(ctorName + "?"), null);
  }
}

public class ValidConstructorNames(Expression root, List<DatatypeCtor> ctors) : ProofObligationDescription {
  public override string SuccessDescription =>
    $"source of datatype update is constructed by {ctorNames}";

  public override string FailureDescription =>
    $"source of datatype update must be constructed by {ctorNames}";

  public override string ShortDescription => "valid constructor names";

  private readonly string ctorNames = DatatypeDestructor.PrintableCtorNameList(ctors, "or");

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return Utils.MakeIsOneCtorAssertion(root, ctors);
  }
}

public class DestructorValid(DatatypeDestructor dtor, Expression root, List<DatatypeCtor> ctors)
  : ProofObligationDescription {
  public override string SuccessDescription =>
    $"destructor '{dtorName}' is only applied to datatype values constructed by {ctorNames}";

  public override string FailureDescription =>
    $"destructor '{dtorName}' can only be applied to datatype values constructed by {ctorNames}";

  public override string ShortDescription => "destructor valid";

  private readonly string dtorName = dtor.Name;
  private readonly string ctorNames = dtor.EnclosingCtorNames("or");

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return Utils.MakeIsOneCtorAssertion(root, ctors);
  }
}

public class NotGhostVariant(string subject, Expression root, List<DatatypeCtor> ctors) : ProofObligationDescription {
  public override string SuccessDescription =>
    $"in a compiled context, {subject} is not applied to a datatype value of a ghost variant (ghost constructor {ctorNames})";

  public override string FailureDescription =>
    $"in a compiled context, {subject} cannot be applied to a datatype value of a ghost variant (ghost constructor {ctorNames})";

  public override string ShortDescription => "not ghost variant";

  private readonly string ctorNames = DatatypeDestructor.PrintableCtorNameList(ctors, "or");

  public NotGhostVariant(string whatKind, string dtorNames, Expression root, List<DatatypeCtor> ctors)
  : this($"{whatKind} {dtorNames}", root, ctors) {
  }

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Not, Utils.MakeIsOneCtorAssertion(root, ctors));
  }
}


//// Misc constraints

public class IndicesInDomain : ProofObligationDescription {
  public override string SuccessDescription =>
    $"all {objType} indices are in the domain of the initialization function";

  public override string FailureDescription =>
    $"all {objType} indices must be in the domain of the initialization function";

  public override string ShortDescription => "indices in domain";

  private readonly string objType;
  private readonly List<Expression> dims;
  private readonly Expression init;

  public IndicesInDomain(string objType, List<Expression> dims, Expression init) {
    Contract.Requires(dims is { Count: > 0 });
    this.objType = objType;
    this.dims = dims;
    this.init = init;
  }

  public override Expression GetAssertedExpr(DafnyOptions options) {
    Utils.MakeQuantifierVarsForDims(dims, out var indexVars, out var indexVarExprs, out var indicesRange);
    var precond = new FunctionCallExpr("requires", init, Token.NoToken, Token.NoToken, new ActualBindings(indexVarExprs));
    return new ForallExpr(Token.NoToken, indexVars, indicesRange, precond, null);
  }
}

public class SubrangeCheck(
  string prefix,
  string sourceType,
  string targetType,
  bool isSubset,
  bool isCertain,
  [CanBeNull] string cause,
  [CanBeNull] Expression check)
  : ProofObligationDescription {
  public override string SuccessDescription =>
    isSubset
      ? $"value always satisfies the subset constraints of '{targetType}'"
      : $"value of expression (of type '{sourceType}') is always an instance of type '{targetType}'";

  public override string FailureDescription => BaseFailureDescription + (isCertain ? "" : cause);

  public override string ShortDescription => "subrange check";

  private string BaseFailureDescription =>
    isSubset
      ? $"{prefix}value does not satisfy the subset constraints of '{targetType}'"
      : $"{prefix}value of expression (of type '{sourceType}') is not known to be an instance of type '{targetType}'" +
        (isCertain ? ", because it might be null" : "");

  private readonly string cause = cause is null ? "" : $" (possible cause: {cause})";
  private readonly Expression check = check;

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return check;
  }
}

public class WitnessCheck(string witnessString, Expression witnessExpr = null) : ProofObligationDescription {
  public override string SuccessDescription =>
    "type is inhabited";

  public override string FailureDescription =>
    witnessString is null
      ? "the given witness expression might not satisfy constraint"
      : (witnessString == "" ? $"{errMsg}{hintMsg}" : $"{errMsg} (only tried {witnessString}){hintMsg}");

  public override string ShortDescription => "witness check";

  public override bool ProvedOutsideUserCode => true;

  private readonly string errMsg = "cannot find witness that shows type is inhabited";
  private readonly string hintMsg =
    "; try giving a hint through a 'witness' or 'ghost witness' clause, or use 'witness *' to treat as a possibly empty type";

  [CanBeNull] private readonly Expression witnessExpr = witnessExpr;

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return witnessExpr ?? base.GetAssertedExpr(options);
  }
}

public class PrefixEqualityLimit(Expression expr) : ProofObligationDescription {
  public override string SuccessDescription =>
    "prefix-equality limit is at least 0";

  public override string FailureDescription =>
    "prefix-equality limit must be at least 0";

  public override string ShortDescription => "prefix-equality limit";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Le, new LiteralExpr(Token.NoToken, 0), expr);
  }
}

public class ForRangeBoundsValid(Expression lo, Expression hi) : ProofObligationDescription {
  public override string SuccessDescription =>
    "lower bound does not exceed upper bound";

  public override string FailureDescription =>
    "lower bound must not exceed upper bound";

  public override string ShortDescription => "for range bounds";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new BinaryExpr(lo.Origin, BinaryExpr.Opcode.Le, lo, hi);
  }
}

public class ForRangeAssignable(ProofObligationDescription desc, Expression expr) : ProofObligationDescription {
  public override string SuccessDescription =>
    "entire range is assignable to index variable";

  public override string FailureDescription =>
    $"entire range must be assignable to index variable, but some {desc.FailureDescription}";

  public override string ShortDescription => "for range assignable";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return expr;
  }
}

public class IsNonRecursive : ProofObligationDescription {
  public override string SuccessDescription =>
    "default value is non-recursive";

  public override string FailureDescription =>
    "default-value expression is not allowed to involve recursive or mutually recursive calls";

  public override string ShortDescription => "default nonrecursive";
}

public class ForallLHSUnique(List<BoundVar> bvars, Expression range, List<Expression> lhsComponents, Expression rhs)
  : ProofObligationDescription {
  public override string SuccessDescription =>
    "left-hand sides of forall-statement bound variables are unique (or right-hand sides are equivalent)";

  public override string FailureDescription =>
    "left-hand sides for different forall-statement bound variables might refer to the same location (and right-hand sides might not be equivalent)";

  public override string ShortDescription => "forall bound unique";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    MakePrimedBoundVarsAndRange(bvars, range, out var primedVars, out var sub, out var combinedRange);
    var combinedVars = bvars.Concat(primedVars).ToList();
    var condition = lhsComponents
      // either at least one LHS component is distinct...
      .Select(lhs => new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Neq, lhs, sub.Substitute(lhs)))
      // ... or the RHS is always the same
      .Append(new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, rhs, sub.Substitute(rhs)))
      .Aggregate((acc, disjunct) => new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Or, acc, disjunct));

    return new ForallExpr(Token.NoToken, combinedVars, combinedRange, condition, null);
  }
}

public class ElementInDomain(Expression sequence, Expression index) : ProofObligationDescription {
  public override string SuccessDescription =>
    "element is in domain";

  public override string FailureDescription =>
    "element might not be in domain";

  public override string ShortDescription => "element in domain";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new BinaryExpr(sequence.Origin, BinaryExpr.Opcode.In,
      index,
      sequence
    );
  }
}

public class DefiniteAssignment(string kind, string name, string where) : ProofObligationDescription {
  public override string SuccessDescription =>
    $"{kind} '{name}', which is subject to definite-assignment rules, is always initialized {where}";

  public override string FailureDescription =>
    $"{kind} '{name}', which is subject to definite-assignment rules, might be uninitialized {where}";

  public override string ShortDescription => "definite assignment";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Assigned, new IdentifierExpr(Token.NoToken, name));
  }
}

public class InRange(Expression sequence, Expression index, bool upperExcluded, string what, int dimension = -1)
  : ProofObligationDescription {
  public override string SuccessDescription => $"{what} in range";

  public override string FailureDescription => $"{what} out of range";

  public override string ShortDescription => "in range";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    if (sequence.Type is SeqType || sequence.Type.IsArrayType) {
      Expression bound = sequence.Type.IsArrayType ?
          new MemberSelectExpr(sequence.Origin, sequence, new Name("Length" + (dimension >= 0 ? "" + dimension : "")))
        : new UnaryOpExpr(sequence.Origin, UnaryOpExpr.Opcode.Cardinality, sequence);
      return new ChainingExpression(sequence.Origin, [
          new LiteralExpr(sequence.Origin, 0),
        index,
        bound
        ], [
          BinaryExpr.Opcode.Le,
          upperExcluded ? BinaryExpr.Opcode.Lt : BinaryExpr.Opcode.Le
        ], [Token.NoToken, Token.NoToken],
        [null, null]);
    }

    return new BinaryExpr(sequence.Origin, BinaryExpr.Opcode.In,
      index,
      sequence
    );
  }
}

public class SequenceSelectRangeValid(Expression sequence, Expression lowerBound, Expression upperBound, string what)
  : ProofObligationDescription {
  public override string SuccessDescription =>
    $"upper bound within range of {what}";

  public override string FailureDescription =>
    $"upper bound below lower bound or above length of {what}";

  public override string ShortDescription => "sequence select range valid";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new ChainingExpression(sequence.Origin, [
      lowerBound,
      upperBound,
      new UnaryOpExpr(sequence.Origin, UnaryOpExpr.Opcode.Cardinality, sequence)
    ], [
      BinaryExpr.Opcode.Le,
      BinaryExpr.Opcode.Le
    ], [Token.NoToken, Token.NoToken], [null, null]);
  }
}

public class ComprehensionNoAlias(List<BoundVar> bvars, Expression range, Expression key, Expression value)
  : ProofObligationDescription {
  public override string SuccessDescription =>
    "key expressions refer to unique values";

  public override string FailureDescription =>
    "key expressions might be referring to the same value";

  public override string ShortDescription => "unique key expressions";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    MakePrimedBoundVarsAndRange(bvars, range, out var primedVars, out var sub, out var combinedRange);
    var combinedVars = bvars.Concat(primedVars).ToList();
    var condition = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Or,
      new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Neq, key, sub.Substitute(key)),
      new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, value, sub.Substitute(value))
    );
    return new ForallExpr(Token.NoToken, combinedVars, combinedRange, condition, null);
  }
}

public class DistinctLHS(string lhsa, string lhsb, bool useMight, bool useWhen, Expression expr)
  : ProofObligationDescription {
  public override string SuccessDescription =>
    $"left-hand sides {lhsa} and {lhsb} are distinct";

  public override string FailureDescription =>
    $"{when}left-hand sides {lhsa} and {lhsb} {might}refer to the same location{whenSuffix}";

  public override string ShortDescription => "distinct lhs";

  private readonly string might = useMight ? "might " : "";
  private readonly string when = useWhen ? "when " : "";
  private readonly string whenSuffix = useWhen ? ", they must be assigned the same value" : "";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return expr;
  }
}

public class ArrayInitSizeValid(TypeRhs rhs, Expression dim) : ProofObligationDescription {
  public override string SuccessDescription =>
    $"given array size agrees with the number of expressions in the initializing display ({size})";

  public override string FailureDescription =>
    $"given array size must agree with the number of expressions in the initializing display ({size})";

  public override string ShortDescription => "array initializer size";

  private int size => rhs.InitDisplay.Count;

  public override Expression GetAssertedExpr(DafnyOptions options) {
    var initDisplaySize = new UnaryOpExpr(rhs.Origin, UnaryOpExpr.Opcode.Cardinality, new SeqDisplayExpr(rhs.Origin, rhs.InitDisplay));
    return new BinaryExpr(dim.Origin, BinaryExpr.Opcode.Eq, dim, initDisplaySize);
  }
}

public class ArrayInitEmpty(string typeDesc, List<Expression> dims) : ProofObligationDescription {
  public override string SuccessDescription =>
    "array initializer has empty size";

  public override string FailureDescription =>
    $"unless an initializer is provided for the array elements, a new array of '{typeDesc}' must have empty size";

  public override string ShortDescription => "array initializer empty";

  private readonly ImmutableList<Expression> dims = dims.ToImmutableList();

  public override Expression GetAssertedExpr(DafnyOptions options) {
    Expression zero = Expression.CreateIntLiteral(dims[0].Origin, 0);
    Expression zeroSize = new BinaryExpr(dims[0].Origin, BinaryExpr.Opcode.Eq, dims[0], zero);
    foreach (Expression dim in dims.Skip(1)) {
      zeroSize = new BinaryExpr(
        dim.Origin,
        BinaryExpr.Opcode.Or,
        zeroSize,
        new BinaryExpr(dim.Origin, BinaryExpr.Opcode.Eq, dim, zero)
      );
    }
    return zeroSize;
  }
}

public class LetSuchThatUnique(Expression condition, List<BoundVar> bvars) : ProofObligationDescription {
  public override string SuccessDescription =>
    "the value of this let-such-that expression is uniquely determined";

  public override string FailureDescription =>
    "to be compilable, the value of a let-such-that expression must be uniquely determined";

  public override string ShortDescription => "let-such-that unique";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    var bvarsExprs = bvars.Select(bvar => new IdentifierExpr(bvar.Origin, bvar)).ToList();
    var substMap = MakePrimedBoundVarSubstMap(bvars, out var bvarprimes, out var bvarprimesExprs);
    var subContract = new Substituter(null, substMap, new Dictionary<TypeParameter, Type>());
    var conditionSecondBoundVar = subContract.Substitute(condition);
    var conclusion = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, bvarsExprs[0], bvarprimesExprs[0]);
    for (var i = 1; i < bvarsExprs.Count; i++) {
      conclusion = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And,
        conclusion,
        new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, bvarsExprs[i], bvarprimesExprs[i])
        );
    }
    return new ForallExpr(Token.NoToken, bvars.Concat(bvarprimes).ToList(),
      new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, condition, conditionSecondBoundVar),

      conclusion, null);
  }
}

public class LetSuchThatExists(List<BoundVar> bvars, Expression condition) : ProofObligationDescription {
  public override string SuccessDescription =>
    "a value exists that satisfies this let-such-that expression";

  public override string FailureDescription =>
    "cannot establish the existence of LHS values that satisfy the such-that predicate";

  public override string ShortDescription => "let-such-that exists";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new ExistsExpr(bvars[0].Origin, bvars,
      null, condition, null);
  }
}

public class AssignmentShrinks(Expression receiver, string fieldName) : ProofObligationDescription {
  public override string SuccessDescription =>
    $"the assignment to {fieldName} always shrinks the set";

  public override string FailureDescription =>
    $"an assignment to {fieldName} is only allowed to shrink the set";

  public override string ShortDescription => "assignment shrinks";

  public override Expression GetAssertedExpr(DafnyOptions options) {
    var receiverDotField = new ExprDotName(Token.NoToken, receiver, new Name(fieldName), null);
    return new BinaryExpr(
      Token.NoToken,
      BinaryExpr.Opcode.And,
      new OldExpr(Token.NoToken, new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Allocated, receiver)),
      new BinaryExpr(Token.NoToken, BinaryExpr.ResolvedOpcode.Subset, receiverDotField, new OldExpr(Token.NoToken, receiverDotField))
    );
  }
}

public class ConcurrentFrameEmpty(MethodOrFunction decl, string frameName) : ProofObligationDescription {
  public override string SuccessDescription =>
    $"{frameName} clause is empty ({{:concurrent}} restriction)";

  public override string FailureDescription =>
    $"{frameName} clause could not be proved to be empty ({{:concurrent}} restriction)";

  public override string ShortDescription => "concurrency safety";

  public override bool ProvedOutsideUserCode => true;

  public override Expression GetAssertedExpr(DafnyOptions options) {
    var bvars = decl.Ins.Select(formal => new BoundVar(formal.Origin, formal.Name, formal.Type)).ToList();
    var func = new ExprDotName(Token.NoToken, new NameSegment(Token.NoToken, decl.Name, null), new Name(frameName), null);
    var args = bvars.Select(bvar => new IdentifierExpr(Token.NoToken, bvar) as Expression).ToList();
    var call = new ApplyExpr(Token.NoToken, func, args, Token.NoToken);
    var isEmpty = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, call,
      new SetDisplayExpr(Token.NoToken, true, []));
    return new ForallExpr(Token.NoToken, bvars, null, isEmpty, null);
  }
}

public class BoilerplateTriple(string errorMessage, string successMessage, string comment)
  : ProofObligationDescriptionCustomMessages(errorMessage, successMessage) {
  public override string ShortDescription => "boilerplate triple";

  public override string DefaultSuccessDescription { get; } = comment;
  public override string DefaultFailureDescription { get; } = comment;
}

internal class Utils {
  public static Expression MakeCharBoundsCheck(DafnyOptions options, Expression expr) {
    return options.Get(CommonOptionBag.UnicodeCharacters)
      ? MakeCharBoundsCheckUnicode(expr)
      : MakeCharBoundsCheckNonUnicode(expr);
  }

  public static Expression MakeCharBoundsCheckNonUnicode(Expression expr) {
    return new BinaryExpr(
      expr.Origin,
      BinaryExpr.Opcode.And,
      new BinaryExpr(
        expr.Origin, BinaryExpr.Opcode.Le, Expression.CreateIntLiteral(Token.NoToken, 0), expr),
      new BinaryExpr(
        expr.Origin, BinaryExpr.Opcode.Lt, expr, Expression.CreateIntLiteral(expr.Origin, 0x1_0000))
    );
  }

  public static Expression MakeCharBoundsCheckUnicode(Expression expr) {
    Expression lowRange = new BinaryExpr(
      expr.Origin,
      BinaryExpr.Opcode.And,
      new BinaryExpr(expr.Origin, BinaryExpr.Opcode.Le, Expression.CreateIntLiteral(Token.NoToken, 0), expr),
      new BinaryExpr(expr.Origin, BinaryExpr.Opcode.Lt, expr, Expression.CreateIntLiteral(expr.Origin, 0xD800))
    );
    Expression highRange = new BinaryExpr(
      expr.Origin,
      BinaryExpr.Opcode.And,
      new BinaryExpr(expr.Origin, BinaryExpr.Opcode.Le, Expression.CreateIntLiteral(Token.NoToken, 0xE000), expr),
      new BinaryExpr(expr.Origin, BinaryExpr.Opcode.Lt, expr, Expression.CreateIntLiteral(expr.Origin, 0x11_0000))
    );
    return new BinaryExpr(lowRange.Origin, BinaryExpr.Opcode.Or, lowRange, highRange);
  }

  public static void MakeQuantifierVarsForDims(List<Expression> dims, out List<BoundVar> vars, out List<Expression> varExprs, out Expression range) {
    var zero = new LiteralExpr(Token.NoToken, 0);
    vars = dims.Select((_, i) => new BoundVar("i" + i, Type.Int)).ToList();

    // can't assign to out-param immediately, since it's accessed in the lambda below
    var tempVarExprs = vars.Select(var => new IdentifierExpr(Token.NoToken, var) as Expression).ToList();
    var indexRanges = dims.Select((dim, i) => new ChainingExpression(
      Token.NoToken,
      [zero, tempVarExprs[i], dim],
      [BinaryExpr.Opcode.Le, BinaryExpr.Opcode.Lt],
      [Token.NoToken, Token.NoToken],
      [null, null]
    ) as Expression).ToList();
    varExprs = tempVarExprs;

    range = dims.Count == 1 ? indexRanges[0] : new ChainingExpression(
      Token.NoToken,
      indexRanges,
      Enumerable.Repeat(BinaryExpr.Opcode.And, dims.Count - 1).ToList(),
      Enumerable.Repeat((IOrigin)Token.NoToken, dims.Count - 1).ToList(),
      Enumerable.Repeat(null as Expression, dims.Count - 1).ToList()
    );
  }

  internal static Expression MakeIsOneCtorAssertion(Expression root, List<DatatypeCtor> ctors) {
    return ctors
      .Select(ctor => new ExprDotName(Token.NoToken, root, ctor.NameNode.Append("?"), null) as Expression)
      .Aggregate((e0, e1) => new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Or, e0, e1));
  }

  /// <summary>
  /// Builds an expression that represents whether (the relevant subset of) the given `supersetFrames`
  /// permit read/modification access to all objects, arrays, and/or sets of objects/arrays in the `subsetFrames`.
  /// </summary>
  public static Expression MakeDafnyMultiFrameCheck(List<FrameExpression> supersetFrames, List<FrameExpression> subsetFrames) {
    if (subsetFrames.Count == 0) {
      return null;
    }
    return subsetFrames
      .Select(target => MakeDafnyFrameCheck(supersetFrames, target.E, target.Field))
      .Aggregate((e0, e1) => new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, e0, e1));
  }

  /// <summary>
  /// Builds an expression that represents whether (the relevant subset of) the given frames
  /// permit read/modification access to an object/array (or set of objects/arrays).
  /// </summary>
  public static Expression MakeDafnyFrameCheck(List<FrameExpression> frames, Expression objOrObjSet, Field field) {
    if (frames.Any(frame => frame.E is WildcardExpr)) {
      return new LiteralExpr(Token.NoToken, true);
    }

    Type objType;
    BoundVar objVar;
    Expression objOperand;
    var isSetObj = objOrObjSet.Type.AsSetType != null;
    if (isSetObj) {
      objType = objOrObjSet.Type.AsSetType.Arg;
      objVar = new BoundVar(Token.NoToken, "obj", objType);
      objOperand = new IdentifierExpr(Token.NoToken, objVar);
    } else {
      objType = objOrObjSet.Type;
      objVar = null;
      objOperand = objOrObjSet;
    }

    var disjuncts = new List<Expression>();
    foreach (var frame in frames) {
      var isSetFrame = frame.E.Type.AsSetType != null;
      var frameObjType = isSetFrame ? frame.E.Type.AsSetType.Arg : frame.E.Type;
      var isTypeRelated =
        objType.IsSubtypeOf(frameObjType, false, false) ||
        frameObjType.IsSubtypeOf(objType, false, false);
      var isFieldRelated = field == null || frame.Field == null || field.Name.Equals(frame.Field.Name);
      if (!(isTypeRelated && isFieldRelated)) {
        continue;
      }

      var relationOp = isSetFrame ? BinaryExpr.Opcode.In : BinaryExpr.Opcode.Eq;
      disjuncts.Add(new BinaryExpr(Token.NoToken, relationOp, objOperand, frame.E));
    }

    if (disjuncts.Count == 0) {
      var emptySet = new SetDisplayExpr(Token.NoToken, true, []);
      disjuncts.Add(new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.In, objOperand, emptySet));
    }

    var check = disjuncts.Aggregate((e0, e1) =>
      new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Or, e0, e1));
    if (!isSetObj) {
      return check;
    }

    return new ForallExpr(
      Token.NoToken,
      [objVar],
      new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.In, objOperand, objOrObjSet),
      check,
      null
    );
  }
}
