#nullable enable
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class AssignmentRhs : NodeWithOrigin, IAttributeBearingDeclaration {
  public Attributes? Attributes { get; set; }

  string IAttributeBearingDeclaration.WhatKind => "assignment right-hand-side";

  public bool HasAttributes() {
    return Attributes != null;
  }

  internal AssignmentRhs(Cloner cloner, AssignmentRhs original) : base(cloner, original) {
    Attributes = cloner.CloneAttributes(original.Attributes);
  }

  [SyntaxConstructor]
  internal AssignmentRhs(IOrigin origin, Attributes? attributes = null) : base(origin) {
    Attributes = attributes;
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