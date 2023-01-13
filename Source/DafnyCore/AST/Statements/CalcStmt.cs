using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class CalcStmt : Statement, ICloneable<CalcStmt> {
  public abstract class CalcOp {
    /// <summary>
    /// Resulting operator "x op z" if "x this y" and "y other z".
    /// Returns null if this and other are incompatible.
    /// </summary>
    [Pure]
    public abstract CalcOp ResultOp(CalcOp other);

    /// <summary>
    /// Returns an expression "line0 this line1".
    /// </summary>
    [Pure]
    public abstract Expression StepExpr(Expression line0, Expression line1);
  }

  public class BinaryCalcOp : CalcOp {
    public readonly BinaryExpr.Opcode Op;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(ValidOp(Op));
    }

    /// <summary>
    /// Is op a valid calculation operator?
    /// </summary>
    [Pure]
    public static bool ValidOp(BinaryExpr.Opcode op) {
      return
        op == BinaryExpr.Opcode.Eq || op == BinaryExpr.Opcode.Neq
                                   || op == BinaryExpr.Opcode.Lt || op == BinaryExpr.Opcode.Le
                                   || op == BinaryExpr.Opcode.Gt || op == BinaryExpr.Opcode.Ge
                                   || LogicOp(op);
    }

    /// <summary>
    /// Is op a valid operator only for Boolean lines?
    /// </summary>
    [Pure]
    public static bool LogicOp(BinaryExpr.Opcode op) {
      return op == BinaryExpr.Opcode.Iff || op == BinaryExpr.Opcode.Imp || op == BinaryExpr.Opcode.Exp;
    }

    public BinaryCalcOp(BinaryExpr.Opcode op) {
      Contract.Requires(ValidOp(op));
      Op = op;
    }

    /// <summary>
    /// Does this subsume other (this . other == other . this == this)?
    /// </summary>
    private bool Subsumes(BinaryCalcOp other) {
      Contract.Requires(other != null);
      var op1 = Op;
      var op2 = other.Op;
      if (op1 == BinaryExpr.Opcode.Neq || op2 == BinaryExpr.Opcode.Neq) {
        return op2 == BinaryExpr.Opcode.Eq;
      }

      if (op1 == op2) {
        return true;
      }

      if (LogicOp(op1) || LogicOp(op2)) {
        return op2 == BinaryExpr.Opcode.Eq ||
               (op1 == BinaryExpr.Opcode.Imp && op2 == BinaryExpr.Opcode.Iff) ||
               (op1 == BinaryExpr.Opcode.Exp && op2 == BinaryExpr.Opcode.Iff) ||
               (op1 == BinaryExpr.Opcode.Eq && op2 == BinaryExpr.Opcode.Iff);
      }

      return op2 == BinaryExpr.Opcode.Eq ||
             (op1 == BinaryExpr.Opcode.Lt && op2 == BinaryExpr.Opcode.Le) ||
             (op1 == BinaryExpr.Opcode.Gt && op2 == BinaryExpr.Opcode.Ge);
    }

    public override CalcOp ResultOp(CalcOp other) {
      if (other is BinaryCalcOp) {
        var o = (BinaryCalcOp)other;
        if (this.Subsumes(o)) {
          return this;
        } else if (o.Subsumes(this)) {
          return other;
        }
        return null;
      } else if (other is TernaryCalcOp) {
        return other.ResultOp(this);
      } else {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }
    }

    public override Expression StepExpr(Expression line0, Expression line1) {
      if (Op == BinaryExpr.Opcode.Exp) {
        // The order of operands is reversed so that it can be turned into implication during resolution
        return new BinaryExpr(line0.tok, Op, line1, line0);
      } else {
        return new BinaryExpr(line0.tok, Op, line0, line1);
      }
    }

    public override string ToString() {
      return BinaryExpr.OpcodeString(Op);
    }

  }

  public class TernaryCalcOp : CalcOp {
    public readonly Expression Index; // the only allowed ternary operator is ==#, so we only store the index

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Index != null);
    }

    public TernaryCalcOp(Expression idx) {
      Contract.Requires(idx != null);
      Index = idx;
    }

    public override CalcOp ResultOp(CalcOp other) {
      if (other is BinaryCalcOp) {
        if (((BinaryCalcOp)other).Op == BinaryExpr.Opcode.Eq) {
          return this;
        }
        return null;
      } else if (other is TernaryCalcOp) {
        var a = Index;
        var b = ((TernaryCalcOp)other).Index;
        var minIndex = new ITEExpr(a.tok, false, new BinaryExpr(a.tok, BinaryExpr.Opcode.Le, a, b), a, b);
        return new TernaryCalcOp(minIndex); // ToDo: if we could compare expressions for syntactic equalty, we could use this here to optimize
      } else {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }
    }

    public override Expression StepExpr(Expression line0, Expression line1) {
      return new TernaryExpr(line0.tok, TernaryExpr.Opcode.PrefixEqOp, Index, line0, line1);
    }

    public override string ToString() {
      return "==#";
    }

  }

  public readonly List<Expression> Lines;    // Last line is dummy, in order to form a proper step with the dangling hint
  public readonly List<BlockStmt> Hints;     // Hints[i] comes after line i; block statement is used as a container for multiple sub-hints
  public readonly CalcOp UserSuppliedOp;     // may be null, if omitted by the user
  public CalcOp Op;                          // main operator of the calculation (either UserSuppliedOp or (after resolution) an inferred CalcOp)
  public readonly List<CalcOp/*?*/> StepOps; // StepOps[i] comes after line i
  [FilledInDuringResolution] public readonly List<Expression> Steps;    // expressions li op l<i + 1> (last step is dummy)
  [FilledInDuringResolution] public Expression Result;                  // expression l0 ResultOp ln

  public static readonly CalcOp DefaultOp = new BinaryCalcOp(BinaryExpr.Opcode.Eq);

  public override IEnumerable<INode> Children => Steps.Concat(new INode[] { Result }).Concat(Hints);

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Lines != null);
    Contract.Invariant(cce.NonNullElements(Lines));
    Contract.Invariant(Hints != null);
    Contract.Invariant(cce.NonNullElements(Hints));
    Contract.Invariant(StepOps != null);
    Contract.Invariant(Steps != null);
    Contract.Invariant(cce.NonNullElements(Steps));
    Contract.Invariant(Hints.Count == Math.Max(Lines.Count - 1, 0));
    Contract.Invariant(StepOps.Count == Hints.Count);
  }

  public CalcStmt(IToken tok, RangeToken rangeToken, CalcOp userSuppliedOp, List<Expression> lines, List<BlockStmt> hints, List<CalcOp/*?*/> stepOps, Attributes attrs)
    : base(tok, rangeToken) {
    Contract.Requires(tok != null);
    Contract.Requires(rangeToken != null);
    Contract.Requires(lines != null);
    Contract.Requires(hints != null);
    Contract.Requires(stepOps != null);
    Contract.Requires(cce.NonNullElements(lines));
    Contract.Requires(cce.NonNullElements(hints));
    Contract.Requires(hints.Count == Math.Max(lines.Count - 1, 0));
    Contract.Requires(stepOps.Count == hints.Count);
    this.UserSuppliedOp = userSuppliedOp;
    this.Lines = lines;
    this.Hints = hints;
    Steps = new List<Expression>();
    this.StepOps = stepOps;
    this.Result = null;
    this.Attributes = attrs;
  }

  public CalcStmt Clone(Cloner cloner) {
    return new CalcStmt(cloner, this);
  }

  public CalcStmt(Cloner cloner, CalcStmt original) : base(cloner, original) {
    // calc statements have the unusual property that the last line is duplicated.  If that is the case (which
    // we expect it to be here), we share the clone of that line as well.
    var lineCount = original.Lines.Count;
    var lines = new List<Expression>(lineCount);
    for (int i = 0; i < lineCount; i++) {
      lines.Add(i == lineCount - 1 && 2 <= lineCount && original.Lines[i] == original.Lines[i - 1] ? lines[i - 1] : cloner.CloneExpr(original.Lines[i]));
    }
    UserSuppliedOp = cloner.CloneCalcOp(original.UserSuppliedOp);
    Lines = lines;
    StepOps = original.StepOps.ConvertAll(cloner.CloneCalcOp);
    Hints = original.Hints.ConvertAll(cloner.CloneBlockStmt);

    if (cloner.CloneResolvedFields) {
      Steps = original.Steps.Select(cloner.CloneExpr).ToList();
      Result = cloner.CloneExpr(original.Result);
      Op = original.Op;
    } else {
      Steps = new List<Expression>();
    }
  }

  public override IEnumerable<Statement> SubStatements {
    get {
      foreach (var h in Hints) {
        yield return h;
      }
    }
  }
  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      foreach (var e in Attributes.SubExpressions(Attributes)) { yield return e; }

      for (int i = 0; i < Lines.Count - 1; i++) {  // note, we skip the duplicated line at the end
        yield return Lines[i];
      }
      foreach (var calcop in AllCalcOps) {
        if (calcop is TernaryCalcOp o3) {
          yield return o3.Index;
        }
      }
    }
  }

  IEnumerable<CalcOp> AllCalcOps {
    get {
      if (UserSuppliedOp != null) {
        yield return UserSuppliedOp;
      }
      foreach (var stepop in StepOps) {
        if (stepop != null) {
          yield return stepop;
        }
      }
    }
  }

  /// <summary>
  /// Left-hand side of a step expression.
  /// Note that Lhs(op.StepExpr(line0, line1)) != line0 when op is <==.
  /// </summary>
  public static Expression Lhs(Expression step) {
    Contract.Requires(step is BinaryExpr || step is TernaryExpr);
    if (step is BinaryExpr) {
      return ((BinaryExpr)step).E0;
    } else {
      return ((TernaryExpr)step).E1;
    }
  }

  /// <summary>
  /// Right-hand side of a step expression.
  /// Note that Rhs(op.StepExpr(line0, line1)) != line1 when op is REVERSE-IMPLICATION.
  /// </summary>
  public static Expression Rhs(Expression step) {
    Contract.Requires(step is BinaryExpr || step is TernaryExpr);
    if (step is BinaryExpr) {
      return ((BinaryExpr)step).E1;
    } else {
      return ((TernaryExpr)step).E2;
    }
  }
}