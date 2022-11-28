using System.Numerics;

namespace Microsoft.Dafny;

/// <summary>
/// This class's code contains helpers that help verifying assertions without
/// the use of Boogie
/// See Translator.IsExprAlways for a smaller version for Boogie expressions
/// </summary>
public static class QuickVerifier {
  // Determines heuristically if a given expression has always the given truth value
  // "false" means "Don't know", whereas "true" means `q` always evaluate to `truth`.
  public static bool IsExpressionAlways(Expression q, bool truth) {
    q = q.WasResolved() ? q.Resolved : q;
    if (q is ForallExpr forallExpr) {
      return truth && IsExpressionAlways(Expression.CreateImplies(
        forallExpr.Range ?? Expression.CreateBoolLiteral(Token.NoToken, true), forallExpr.Term, true), true);
    }
    if (q is ExistsExpr existsExpr) {
      return !truth && IsExpressionAlways(Expression.CreateAnd(
        existsExpr.Range ?? Expression.CreateBoolLiteral(Token.NoToken, true), existsExpr.Term, true), false);
    }
    if (q is LiteralExpr { Value: bool value } && value == truth) {
      return true;
    }

    if (q is UnaryOpExpr unaryOpExpr && unaryOpExpr.Op == UnaryOpExpr.Opcode.Not) {
      return IsExpressionAlways(unaryOpExpr.E, !truth);
    }
    if (q is BinaryExpr binaryExpr) {
      var e0 = binaryExpr.E0;
      var e1 = binaryExpr.E1;
      switch (binaryExpr.Op) {
        case BinaryExpr.Opcode.And:
          return truth
            ? IsExpressionAlways(e0, true) && IsExpressionAlways(e1, true)
            : IsExpressionAlways(e0, false) || IsExpressionAlways(e1, false);
        case BinaryExpr.Opcode.Or:
          return truth
            ? IsExpressionAlways(e0, true) || IsExpressionAlways(e1, true)
            : IsExpressionAlways(e0, false) && IsExpressionAlways(e1, false);
        case BinaryExpr.Opcode.Imp:
          return truth
            ? IsExpressionAlways(e0, false) || IsExpressionAlways(e1, true)
            : IsExpressionAlways(e0, true) && IsExpressionAlways(e1, false);
        case BinaryExpr.Opcode.Iff:
          return truth
            ? (IsExpressionAlways(e0, false) && IsExpressionAlways(e1, false) || IsExpressionAlways(e0, true) && IsExpressionAlways(e1, true))
            : (IsExpressionAlways(e0, true) && IsExpressionAlways(e1, false) || IsExpressionAlways(e0, false) && IsExpressionAlways(e1, true));
        case BinaryExpr.Opcode.Eq:
          if (truth) { // Obvious case when A == B is true, when the two representations are the same.
            return
              e0.Type is BoolType && IsExpressionAlways(
                new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Iff, e0, e1)
                , true) || Printer.ExprToString(e0) == Printer.ExprToString(e1);
          } else {
            // Cases in which we absolutely know that an equality can't hold
            // - One expression is a datatype and the other is destructing this datatype
            // - Two literals that are different
            if (e0 is LiteralExpr { Value: BigInteger b1 } && e1 is LiteralExpr { Value: BigInteger b2 }) {
              return b1.CompareTo(b2) != 0;
            }
            if (e0 is LiteralExpr { Value: bool bb1 } && e1 is LiteralExpr { Value: bool bb2 }) {
              return bb1 != bb2;
            }
            if (!truth &&
                e0.Type.NormalizeExpand().AsIndDatatype is IndDatatypeDecl
                && e1.Type.NormalizeExpand().AsIndDatatype is IndDatatypeDecl
                && Printer.ExprToString(e0) is var e0str
                && Printer.ExprToString(e1) is var e1str
                && (e1str.StartsWith(e0str + ".") || (e0str.StartsWith(e1str + ".")))) {
              return true;
            }
            return false;
          }
        case BinaryExpr.Opcode.Lt: {
            if (!truth && Printer.ExprToString(e0) == Printer.ExprToString(e1)) { // Obvious case when A < B is wrong: B == A
              return true;
            }
            // Obvious case when A < B is always true, when A and B are bigintegers
            if (e0 is LiteralExpr { Value: BigInteger b1 } && e1 is LiteralExpr { Value: BigInteger b2 }) {
              return truth == (b1.CompareTo(b2) < 0);
            }
            return false;
          }
        case BinaryExpr.Opcode.Gt: {
            // Obvious case when A > B is wrong: B == A
            if (!truth && Printer.ExprToString(e0) == Printer.ExprToString(e1)) {
              return true;
            }
            // Obvious case when A > B is always true, when A and B are bigintegers
            if (e0 is LiteralExpr { Value: BigInteger b1 } lit1 && e1 is LiteralExpr { Value: BigInteger b2 }) {
              return truth == (b1.CompareTo(b2) > 0);
            }
            return false;
          }
        case BinaryExpr.Opcode.Neq: {
            // Obvious case when A != B is wrong: B == A
            if (!truth && Printer.ExprToString(e0) == Printer.ExprToString(e1)) {
              return true;
            }
            // Obvious case when A > B is always true, when A and B are bigintegers
            if (e0 is LiteralExpr { Value: var value1 } && e1 is LiteralExpr { Value: var value2 }) {
              if (value1 is BigInteger b1 && value2 is BigInteger b2) {
                return truth == (b1.CompareTo(b2) != 0);
              } else if (value1 is bool bb1 && value2 is bool bb2) {
                return truth == (bb1 != bb2);
              }
            }
            if (truth
                && e0.Type.NormalizeExpand().AsIndDatatype is IndDatatypeDecl
                && e1.Type.NormalizeExpand().AsIndDatatype is IndDatatypeDecl
                && Printer.ExprToString(e0) is var e0str
                && Printer.ExprToString(e1) is var e1str
                && (e1str.StartsWith(e0str + ".") || (e0str.StartsWith(e1str + ".")))) {
              return true;
            }

            return false;
          }
      }
    }

    return false;
  }
}