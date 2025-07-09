#nullable enable

using System.Collections.Generic;
using System.Diagnostics;

namespace Microsoft.Dafny;

public class BoundVar : NonglobalVariable {
  public override bool IsMutable => false;

  public BoundVar(IOrigin origin, string name, Type? syntacticType = null, bool isGhost = false)
    : this(origin, new Name(origin.Center, name), syntacticType, isGhost) { }

  [SyntaxConstructor]
  public BoundVar(IOrigin origin, Name nameNode, Type? syntacticType = null, bool isGhost = false)
    : base(origin, nameNode, syntacticType, isGhost) { }

  public BoundVar(Cloner cloner, BoundVar original) : base(cloner, original) {
  }
}

/// <summary>
/// A QuantifiedVar is a bound variable used in a quantifier such as "forall x :: ...",
/// a comprehension such as "set x | 0 <= x < 10", etc.
/// In addition to its type, which may be inferred, it can have an optional domain collection expression
/// (x <- C) and an optional range boolean expressions (x | E).
/// </summary>
[DebuggerDisplay("Quantified<{name}>")]
[SyntaxBaseType(typeof(NodeWithOrigin))]
public class QuantifiedVar : BoundVar {
  public Expression? Domain;
  public Expression? Range;

  public QuantifiedVar(IOrigin origin, string name, Type? syntacticType, Expression? domain, Expression? range)
    : base(origin, name, syntacticType) {
    Domain = domain;
    Range = range;
  }

  [SyntaxConstructor]
  public QuantifiedVar(IOrigin origin, Name nameNode, Type? syntacticType, Expression? domain, Expression? range)
    : base(origin, nameNode, syntacticType) {
    Domain = domain;
    Range = range;
  }

  /// <summary>
  /// Map a list of quantified variables to an equivalent list of bound variables plus a single range expression.
  /// The transformation looks like this in general:
  /// 
  /// <code><![CDATA[
  /// 
  /// x1 <- C1 | E1, ..., xN <- CN | EN
  /// 
  /// ]]></code>
  ///
  /// becomes:
  ///
  /// <code><![CDATA[
  /// 
  /// x1, ... xN | x1 in C1 && E1 && ... && xN in CN && EN
  /// 
  /// ]]></code>
  ///
  /// Note the result will be null rather than "true" if there are no such domains or ranges.
  /// Some quantification contexts (such as comprehensions) will replace this with "true".
  /// </summary>
  public static void ExtractSingleRange(List<QuantifiedVar> qvars, out List<BoundVar> bvars, out Expression? range) {
    bvars = [];
    range = null;

    foreach (var qvar in qvars) {
      BoundVar bvar = new BoundVar(qvar.Origin, qvar.Name, qvar.SyntacticType);
      bvars.Add(bvar);

      if (qvar.Domain != null) {
        // Attach a token wrapper so we can produce a better error message if the domain is not a collection
        var domainWithToken = QuantifiedVariableDomainCloner.Instance.CloneExpr(qvar.Domain);
        var inDomainExpr = new BinaryExpr(domainWithToken.Origin.Center, BinaryExpr.Opcode.In, new IdentifierExpr(bvar.Origin, bvar), domainWithToken);
        range = range == null ? inDomainExpr : new BinaryExpr(domainWithToken.Origin.Center, BinaryExpr.Opcode.And, range, inDomainExpr);
      }

      if (qvar.Range != null) {
        // Attach a token wrapper so we can produce a better error message if the range is not a boolean expression
        var rangeWithToken = QuantifiedVariableRangeCloner.Instance.CloneExpr(qvar.Range);
        range = range == null ? qvar.Range : new BinaryExpr(rangeWithToken.Origin.Center, BinaryExpr.Opcode.And, range, rangeWithToken);
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
  public static QuantifiedVariableDomainCloner Instance = new QuantifiedVariableDomainCloner();
  private QuantifiedVariableDomainCloner() { }
  public override IOrigin? Origin(IOrigin? tok) {
    if (tok == null) {
      return null;
    }

    return new QuantifiedVariableDomainOrigin(tok);
  }
}

class QuantifiedVariableRangeCloner : Cloner {
  public static QuantifiedVariableRangeCloner Instance = new QuantifiedVariableRangeCloner();
  private QuantifiedVariableRangeCloner() { }
  public override IOrigin? Origin(IOrigin? tok) {
    if (tok == null) {
      return null;
    }

    return new QuantifiedVariableRangeOrigin(tok);
  }
}