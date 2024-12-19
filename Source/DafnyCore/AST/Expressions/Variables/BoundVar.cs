using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

public class BoundVar : NonglobalVariable {
  public override bool IsMutable => false;

  public BoundVar(string name, Type type) : this(Token.NoToken, new Name(Token.NoToken, name), type) { }
  public BoundVar(IOrigin origin, string name, Type type) : this(origin, new Name(origin.StartToken, name), type) { }

  public BoundVar(IOrigin tok, Name name, Type type)
    : base(tok, name, type, false) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Contract.Requires(type != null);
  }
}

/// <summary>
/// A QuantifiedVar is a bound variable used in a quantifier such as "forall x :: ...",
/// a comprehension such as "set x | 0 <= x < 10", etc.
/// In addition to its type, which may be inferred, it can have an optional domain collection expression
/// (x <- C) and an optional range boolean expressions (x | E).
/// </summary>
[DebuggerDisplay("Quantified<{name}>")]
public class QuantifiedVar : BoundVar {
  public readonly Expression Domain;
  public readonly Expression Range;

  public QuantifiedVar(IOrigin tok, string name, Type type, Expression domain, Expression range)
    : base(tok, name, type) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Contract.Requires(type != null);
    Domain = domain;
    Range = range;
  }

  /// <summary>
  /// Map a list of quantified variables to an equivalent list of bound variables plus a single range expression.
  /// The transformation looks like this in general:
  ///
  /// x1 <- C1 | E1, ..., xN <- CN | EN
  ///
  /// becomes:
  ///
  /// x1, ... xN | x1 in C1 && E1 && ... && xN in CN && EN
  ///
  /// Note the result will be null rather than "true" if there are no such domains or ranges.
  /// Some quantification contexts (such as comprehensions) will replace this with "true".
  /// </summary>
  public static void ExtractSingleRange(List<QuantifiedVar> qvars, out List<BoundVar> bvars, [CanBeNull] out Expression range) {
    bvars = new List<BoundVar>();
    range = null;

    foreach (var qvar in qvars) {
      BoundVar bvar = new BoundVar(qvar.Tok, qvar.Name, qvar.SyntacticType);
      bvars.Add(bvar);

      if (qvar.Domain != null) {
        // Attach a token wrapper so we can produce a better error message if the domain is not a collection
        var domainWithToken = QuantifiedVariableDomainCloner.Instance.CloneExpr(qvar.Domain);
        var inDomainExpr = new BinaryExpr(domainWithToken.Tok, BinaryExpr.Opcode.In, new IdentifierExpr(bvar.Tok, bvar), domainWithToken);
        range = range == null ? inDomainExpr : new BinaryExpr(domainWithToken.Tok, BinaryExpr.Opcode.And, range, inDomainExpr);
      }

      if (qvar.Range != null) {
        // Attach a token wrapper so we can produce a better error message if the range is not a boolean expression
        var rangeWithToken = QuantifiedVariableRangeCloner.Instance.CloneExpr(qvar.Range);
        range = range == null ? qvar.Range : new BinaryExpr(rangeWithToken.Tok, BinaryExpr.Opcode.And, range, rangeWithToken);
      }
    }
  }
}

/// <summary>
/// An expression introducting bound variables
/// </summary>
public interface IBoundVarsBearingExpression {
  public IEnumerable<BoundVar> AllBoundVars {
    get;
  }
}

class QuantifiedVariableDomainCloner : Cloner {
  public static readonly QuantifiedVariableDomainCloner Instance = new QuantifiedVariableDomainCloner();
  private QuantifiedVariableDomainCloner() { }
  public override IOrigin Origin(IOrigin tok) {
    if (tok == null) {
      return null;
    }

    return new QuantifiedVariableDomainOrigin(tok);
  }
}

class QuantifiedVariableRangeCloner : Cloner {
  public static readonly QuantifiedVariableRangeCloner Instance = new QuantifiedVariableRangeCloner();
  private QuantifiedVariableRangeCloner() { }
  public override IOrigin Origin(IOrigin tok) {
    if (tok == null) {
      return null;
    }

    return new QuantifiedVariableRangeOrigin(tok);
  }
}