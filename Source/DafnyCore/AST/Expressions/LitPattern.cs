using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Numerics;

namespace Microsoft.Dafny;

public class LitPattern : ExtendedPattern {
  public readonly Expression OrigLit;  // the expression as parsed; typically a LiteralExpr, but could be a NegationExpression

  /// <summary>
  /// The patterns of match constructs are rewritten very early during resolution, before any type information
  /// is available. This is unfortunate. It means we can't reliably rewrite negated expressions. In Dafny, "-" followed
  /// by digits is a negative literal for integers and reals, but as unary minus for bitvectors and ORDINAL (and
  /// unary minus is not allowed for ORDINAL, so that should always give an error).
  ///
  /// Since we don't have the necessary type information at this time, we optimistically negate all numeric literals here.
  /// After type checking, we look to see if we negated something we should not have.
  ///
  /// One could imagine allowing negative bitvector literals in case patterns and treating and them as synonyms for their
  /// positive counterparts. However, since the rewriting does not know about these synonyms, it would end up splitting
  /// cases that should have been combined, which leads to incorrect code.
  ///
  /// It would be good to check for these inadvertently allowed unary expressions only in the expanded patterns. However,
  /// the rewriting of patterns turns them into "if" statements and what not, so it's not easy to identify when a literal
  /// comes from this rewrite. Luckily, when other NegationExpressions are resolved, they turn into unary minus for bitvectors
  /// and into errors for ORDINALs. Therefore, any negative bitvector or ORDINAL literal discovered later can only have
  /// come from this rewriting. So, that's where errors are generated.
  ///
  /// One more detail, after the syntactic "-0" has been negated, the result is not negative. Therefore, what the previous
  /// paragraph explained as checking for negative bitvectors and ORDINALs doesn't work for "-0". So, instead of checking
  /// for the number being negative, the later pass will check if the token associated with the literal is "-0", a condition
  /// the assignment below ensures.
  /// </summary>
  public LiteralExpr OptimisticallyDesugaredLit {
    get {
      if (OrigLit is NegationExpression neg) {
        var lit = (LiteralExpr)neg.E;
        if (lit.Value is BaseTypes.BigDec d) {
          return new LiteralExpr(neg.tok, -d);
        } else {
          var n = (BigInteger)lit.Value;
          var tok = new Token(neg.tok.line, neg.tok.col) {
            Filename = neg.tok.Filename,
            val = "-0"
          };
          return new LiteralExpr(tok, -n);
        }
      } else {
        return (LiteralExpr)OrigLit;
      }
    }
  }

  public LitPattern(IToken tok, Expression lit, bool isGhost = false) : base(tok, isGhost) {
    Contract.Requires(lit is LiteralExpr || lit is NegationExpression);
    this.OrigLit = lit;
  }

  public override string ToString() {
    return Printer.ExprToString(OrigLit);
  }

  public override IEnumerable<INode> Children => new[] { OrigLit };
}