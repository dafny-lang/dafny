using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class Statement : RangeNode, IAttributeBearingDeclaration {
  public override IToken Tok => PostLabelToken ?? StartToken;
  public IToken PostLabelToken { get; set; }

  public LList<Label> Labels;  // mutable during resolution

  private Attributes attributes;
  public Attributes Attributes {
    get {
      return attributes;
    }
    set {
      attributes = value;
    }
  }

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Tok != null);
  }

  [FilledInDuringResolution] public bool IsGhost { get; set; }

  public virtual void Resolve(ModuleResolver resolver, ResolutionContext resolutionContext) {
    resolver.ResolveAttributes(this, resolutionContext);
  }

  protected Statement(Cloner cloner, Statement original) : base(cloner.Tok(original.RangeToken)) {
    cloner.AddStatementClone(original, this);
    this.attributes = cloner.CloneAttributes(original.Attributes);

    if (cloner.CloneResolvedFields) {
      IsGhost = original.IsGhost;
      Labels = original.Labels;
    }
  }

  protected Statement(RangeToken rangeToken, Attributes attrs) : base(rangeToken) {
    this.attributes = attrs;
  }

  protected Statement(RangeToken rangeToken)
    : this(rangeToken, null) {
    Contract.Requires(rangeToken != null);
  }

  /// <summary>
  /// Returns the non-null expressions of this statement proper (that is, do not include the expressions of substatements).
  /// Filters all sub expressions that are not part of specifications
  /// </summary>
  public IEnumerable<Expression> SubExpressionsIncludingTransitiveSubStatements {
    get {
      foreach (var e in SubExpressions) {
        yield return e;
      }

      foreach (var s in SubStatements) {
        foreach (var e in s.SubExpressionsIncludingTransitiveSubStatements) {
          yield return e;
        }
      }
    }
  }

  /// <summary>
  /// Returns the non-null substatements of the Statements.
  /// </summary>
  public virtual IEnumerable<Statement> SubStatements {
    get { yield break; }
  }

  /// <summary>
  /// Returns the non-null substatements of the Statements, before resolution occurs
  /// </summary>
  public virtual IEnumerable<Statement> PreResolveSubStatements => SubStatements;

  /// <summary>
  /// Returns the non-null expressions of this statement proper (that is, do not include the expressions of substatements).
  /// Includes both specification and non-specification expressions.
  /// </summary>
  public IEnumerable<Expression> SubExpressions {
    get {
      foreach (var e in SpecificationSubExpressions) {
        yield return e;
      }

      foreach (var e in NonSpecificationSubExpressions) {
        yield return e;
      }
    }
  }

  /// <summary>
  /// Same as SubExpressions but returns all the SubExpressions before resolution
  /// </summary>
  public virtual IEnumerable<Expression> PreResolveSubExpressions => SubExpressions;

  /// <summary>
  /// Returns the non-null expressions of this statement proper (that is, do not include the expressions of substatements).
  /// Filters only expressions that are always part of specifications
  /// </summary>
  public virtual IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in Attributes.SubExpressions(Attributes)) {
        yield return e;
      }
    }
  }

  /// <summary>
  /// Returns the non-null expressions of this statement proper (that is, do not include the expressions of substatements).
  /// Filters all sub expressions that are not part of specifications
  /// </summary>
  public virtual IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      yield break;
    }
  }

  /// <summary>
  /// Create a resolved statement for an uninitialized local variable.
  /// </summary>
  public static VarDeclStmt CreateLocalVariable(IToken tok, string name, Type type) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Contract.Requires(type != null);
    var variable = new LocalVariable(tok.ToRange(), name, type, false);
    variable.type = type;
    return new VarDeclStmt(tok.ToRange(), Util.Singleton(variable), null);
  }

  /// <summary>
  /// Create a resolved statement for a local variable with an initial value.
  /// </summary>
  public static VarDeclStmt CreateLocalVariable(IToken tok, string name, Expression value) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Contract.Requires(value != null);
    var rangeToken = new RangeToken(tok, tok);
    var variable = new LocalVariable(rangeToken, name, value.Type, false);
    variable.type = value.Type;
    Expression variableExpr = new IdentifierExpr(tok, variable);
    var variableUpdateStmt = new UpdateStmt(rangeToken, Util.Singleton(variableExpr),
      Util.Singleton<AssignmentRhs>(new ExprRhs(value)));
    var variableAssignStmt = new AssignStmt(rangeToken, variableUpdateStmt.Lhss[0], variableUpdateStmt.Rhss[0]);
    variableUpdateStmt.ResolvedStatements = new List<Statement>() { variableAssignStmt };
    return new VarDeclStmt(rangeToken, Util.Singleton(variable), variableUpdateStmt);
  }

  public static PrintStmt CreatePrintStmt(IToken tok, params Expression[] exprs) {
    var rangeToken = new RangeToken(tok, tok);
    return new PrintStmt(rangeToken, exprs.ToList());
  }

  public override string ToString() {
    try {
      return Printer.StatementToString(DafnyOptions.DefaultImmutableOptions, this);
    } catch (Exception e) {
      return $"couldn't print stmt because: {e.Message}";
    }
  }

  public override IEnumerable<Node> Children =>
    (Attributes != null ? new List<Node> { Attributes } : Enumerable.Empty<Node>()).Concat(
      SubStatements.Concat<Node>(SubExpressions));

  public override IEnumerable<Node> PreResolveChildren =>
    (Attributes != null ? new List<Node> { Attributes } : Enumerable.Empty<Node>()).Concat(
      PreResolveSubStatements).Concat(PreResolveSubExpressions);
}