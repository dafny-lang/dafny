using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class AssignmentRhs : TokenNode, IAttributeBearingDeclaration {
  private Attributes attributes;

  public Attributes Attributes {
    get { return attributes; }
    set { attributes = value; }
  }
  string IAttributeBearingDeclaration.WhatKind => "assignment right-hand-side";

  public bool HasAttributes() {
    return Attributes != null;
  }

  internal AssignmentRhs(Cloner cloner, AssignmentRhs original) {
    tok = cloner.Origin(original.Tok);
    Attributes = cloner.CloneAttributes(original.Attributes);
    Origin = cloner.Origin(original.RangeOrigin);
  }

  internal AssignmentRhs(IOrigin tok, Attributes attrs = null) {
    this.tok = tok;
    Attributes = attrs;
  }

  public abstract bool CanAffectPreviouslyKnownExpressions { get; }

  /// <summary>
  /// Returns all (specification and non-specification) non-null expressions of the AssignmentRhs.
  /// </summary>
  public IEnumerable<Expression> SubExpressions => SpecificationSubExpressions.Concat(NonSpecificationSubExpressions);

  /// <summary>
  /// Returns the non-null non-specification subexpressions of the AssignmentRhs.
  /// </summary>
  public virtual IEnumerable<Expression> NonSpecificationSubExpressions {
    get { yield break; }
  }

  /// <summary>
  /// Returns the non-null specification subexpressions of the AssignmentRhs.
  /// </summary>
  public virtual IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in Attributes.SubExpressions(Attributes)) {
        yield return e;
      }
    }
  }

  /// <summary>
  /// Returns the non-null subexpressions before resolution of the AssignmentRhs.
  /// </summary>
  public virtual IEnumerable<Expression> PreResolveSubExpressions {
    get {
      foreach (var e in Attributes.SubExpressions(Attributes)) {
        yield return e;
      }
    }
  }

  /// <summary>
  /// Returns the non-null sub-statements of the AssignmentRhs.
  /// </summary>
  public virtual IEnumerable<Statement> SubStatements {
    get { yield break; }
  }

  public virtual IEnumerable<Statement> PreResolveSubStatements => SubStatements;
}