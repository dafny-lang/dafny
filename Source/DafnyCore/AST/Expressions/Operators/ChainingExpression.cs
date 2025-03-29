#nullable enable

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class ChainingExpression : ConcreteSyntaxExpression, ICloneable<ChainingExpression>, ICanFormat {
  public List<Expression> Operands;
  public List<BinaryExpr.Opcode> Operators;
  public List<IOrigin> OperatorLocs;
  public List<Expression?> PrefixLimits;
  public Expression E;

  public ChainingExpression Clone(Cloner cloner) {
    return new ChainingExpression(cloner, this);
  }

  public ChainingExpression(Cloner cloner, ChainingExpression original) : base(cloner, original) {
    Operands = original.Operands.Select(cloner.CloneExpr).ToList();
    Operators = original.Operators;
    OperatorLocs = original.OperatorLocs.Select(cloner.Origin).ToList();
    PrefixLimits = original.PrefixLimits.Select(cloner.CloneExpr).ToList();
    E = ComputeDesugaring(Operands, Operators, OperatorLocs, PrefixLimits);
  }

  [SyntaxConstructor]
  public ChainingExpression(IOrigin origin, List<Expression> operands, List<BinaryExpr.Opcode> operators, List<IOrigin> operatorLocs, List<Expression?> prefixLimits)
    : base(origin) {
    Contract.Requires(1 <= operators.Count);
    Contract.Requires(operands.Count == operators.Count + 1);
    Contract.Requires(operatorLocs.Count == operators.Count);
    Contract.Requires(prefixLimits.Count == operators.Count);
    // Additional preconditions apply, see Contract.Assume's below

    Operands = operands;
    Operators = operators;
    OperatorLocs = operatorLocs;
    PrefixLimits = prefixLimits;
    E = ComputeDesugaring(operands, operators, operatorLocs, prefixLimits);
  }

  private static Expression ComputeDesugaring(List<Expression> operands, List<BinaryExpr.Opcode> operators, List<IOrigin> operatorLocs, List<Expression?> prefixLimits) {
    Expression? desugaring;
    // Compute the desugaring
    if (operators[0] == BinaryExpr.Opcode.Disjoint) {
      Expression acc = operands[0]; // invariant:  "acc" is the union of all operands[j] where j <= i
      desugaring = new BinaryExpr(operatorLocs[0], operators[0], operands[0], operands[1]);
      for (int i = 0; i < operators.Count; i++) {
        Contract.Assume(operators[i] == BinaryExpr.Opcode.Disjoint);
        var opTok = operatorLocs[i];
        var e = new BinaryExpr(opTok, BinaryExpr.Opcode.Disjoint, acc, operands[i + 1]);
        desugaring = new BinaryExpr(opTok, BinaryExpr.Opcode.And, desugaring, e);
        acc = new BinaryExpr(opTok, BinaryExpr.Opcode.Add, acc, operands[i + 1]);
      }
    } else {
      desugaring = null;
      for (int i = 0; i < operators.Count; i++) {
        var opTok = operatorLocs[i];
        var op = operators[i];
        Contract.Assume(op != BinaryExpr.Opcode.Disjoint);
        var k = prefixLimits[i];
        Contract.Assume(k == null || op == BinaryExpr.Opcode.Eq || op == BinaryExpr.Opcode.Neq);
        var e0 = operands[i];
        var e1 = operands[i + 1];
        Expression e;
        if (k == null) {
          e = new BinaryExpr(opTok, op, e0, e1);
        } else {
          e = new TernaryExpr(opTok,
            op == BinaryExpr.Opcode.Eq ? TernaryExpr.Opcode.PrefixEqOp : TernaryExpr.Opcode.PrefixNeqOp, k, e0,
            e1);
        }

        desugaring = desugaring == null ? e : new BinaryExpr(opTok, BinaryExpr.Opcode.And, desugaring, e);
      }
    }

    return desugaring!;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      if (!WasResolved()) {
        foreach (var sub in PreResolveSubExpressions) {
          yield return sub;
        }
      } else {
        yield return Resolved;
      }
    }
  }
  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      foreach (var sub in Operands) {
        yield return sub;
      }
      foreach (var sub in PrefixLimits) {
        if (sub != null) {
          yield return sub;
        }
      }
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    // Chaining expressions try to align their values if possible
    var itemIndent = formatter.GetNewTokenVisualIndent(
      Operands[0].StartToken, indentBefore);

    foreach (var token in OwnedTokens) {
      switch (token.val) {
        case "[":
          break;
        case "#":
          break;
        case "]":
          break;
        default:
          formatter.SetIndentations(token, itemIndent, Math.Max(itemIndent - token.val.Length - 1, 0), itemIndent);
          break;
      }
    }

    return true;
  }
}