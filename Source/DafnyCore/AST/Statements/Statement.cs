using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class Statement : RangeNode, IAttributeBearingDeclaration {
  public override IOrigin Tok => PostLabelToken ?? Origin;
  public IOrigin PostLabelToken { get; set; }

  public int ScopeDepth { get; set; }
  public LList<Label> Labels;  // mutable during resolution

  public Attributes Attributes { get; set; }
  string IAttributeBearingDeclaration.WhatKind => "statement";

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Tok != null);
  }

  [FilledInDuringResolution] public bool IsGhost { get; set; }

  public virtual void GenResolve(INewOrOldResolver resolver, ResolutionContext resolutionContext) {
    resolver.ResolveAttributes(this, resolutionContext);
  }

  protected Statement(Cloner cloner, Statement original) : base(cloner.Origin(original.Origin)) {
    cloner.AddStatementClone(original, this);
    this.Attributes = cloner.CloneAttributes(original.Attributes);

    if (cloner.CloneResolvedFields) {
      IsGhost = original.IsGhost;
      Labels = original.Labels;
    }
  }

  protected Statement(IOrigin rangeOrigin, Attributes attrs) : base(rangeOrigin) {
    this.Attributes = attrs;
  }

  protected Statement(IOrigin rangeOrigin)
    : this(rangeOrigin, null) {
    Contract.Requires(rangeOrigin != null);
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

  public IEnumerable<Statement> DescendantsAndSelf {
    get {
      Stack<Statement> todo = new();
      List<Statement> result = new();
      todo.Push(this);
      while (todo.Any()) {
        var current = todo.Pop();
        result.Add(current);
        foreach (var child in current.SubStatements) {
          todo.Push(child);
        }
      }

      return result;
    }
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
  public static VarDeclStmt CreateLocalVariable(IOrigin tok, string name, Type type) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Contract.Requires(type != null);
    var variable = new LocalVariable(tok, name, type, false);
    variable.type = type;
    return new VarDeclStmt(tok, Util.Singleton(variable), null);
  }

  /// <summary>
  /// Create a resolved statement for a local variable with an initial value.
  /// </summary>
  public static VarDeclStmt CreateLocalVariable(IOrigin tok, string name, Expression value) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Contract.Requires(value != null);
    var variable = new LocalVariable(tok, name, value.Type, false);
    variable.type = value.Type;
    Expression variableExpr = new IdentifierExpr(tok, variable);
    var variableUpdateStmt = new AssignStatement(tok, Util.Singleton(variableExpr),
      Util.Singleton<AssignmentRhs>(new ExprRhs(value)));
    var variableAssignStmt = new SingleAssignStmt(tok, variableUpdateStmt.Lhss[0], variableUpdateStmt.Rhss[0]);
    variableUpdateStmt.ResolvedStatements = new List<Statement>() { variableAssignStmt };
    return new VarDeclStmt(tok, Util.Singleton(variable), variableUpdateStmt);
  }

  public static PrintStmt CreatePrintStmt(IOrigin tok, params Expression[] exprs) {
    return new PrintStmt(tok, exprs.ToList());
  }

  public override string ToString() {
    try {
      return Printer.StatementToString(DafnyOptions.DefaultImmutableOptions, this);
    } catch (Exception e) {
      return $"couldn't print stmt because: {e.Message}";
    }
  }

  public override IEnumerable<INode> Children =>
    Attributes.AsEnumerable().
      Concat<Node>(
      SubStatements.Concat<Node>(SubExpressions));

  public override IEnumerable<INode> PreResolveChildren =>
    Attributes.AsEnumerable().
      Concat<Node>(
      PreResolveSubStatements).Concat(PreResolveSubExpressions);

  public virtual IEnumerable<IdentifierExpr> GetAssignedLocals() => Enumerable.Empty<IdentifierExpr>();


  /// <summary>
  /// There are three kinds of contexts for statements.
  ///   - compiled contexts, where the statement must be compilable
  ///     -- !mustBeErasable && proofContext == null
  ///   - ghost contexts that allow the allocation of new object
  ///     -- mustBeErasable && proofContext == null
  ///   - lemma/proof contexts, which are ghost and are not allowed to allocate new objects
  ///     -- mustBeErasable && proofContext != null
  /// 
  /// This method does three things, in order:
  /// 0. Sets .IsGhost to "true" if the statement is ghost.  This often depends on some guard of the statement
  ///    (like the guard of an "if" statement) or the LHS of the statement (if it is an assignment).
  ///    Note, if "mustBeErasable", then the statement is already in a ghost context.
  /// 1. Determines if the statement and all its subparts are legal under its computed .IsGhost setting.
  /// 2. ``Upgrades'' .IsGhost to "true" if, after investigation of the substatements of the statement, it
  ///    turns out that the statement can be erased during compilation.
  /// Notes:
  /// * Both step (0) and step (2) sets the .IsGhost field.  What step (0) does affects only the
  ///   rules of resolution, whereas step (2) makes a note for the later compilation phase.
  /// * It is important to do step (0) before step (1)--that is, it is important to set the statement's ghost
  ///   status before descending into its substatements--because break statements look at the ghost status of
  ///   its enclosing statements.
  /// * The method called by a StmtExpr must be ghost; however, this is checked elsewhere.  For
  ///   this reason, it is not necessary to visit all subexpressions, unless the subexpression
  ///   matter for the ghost checking/recording of "stmt".
  ///
  /// If "proofContext" is non-null, then this method also checks that "stmt" does not allocate
  /// memory or modify the heap, either directly or indirectly using a statement like "modify", a loop with
  /// an explicit "modifies" clause, or a call to a method that may allocate memory or modify the heap.
  /// The "proofContext" string is something that can be printed as part of an error message.
  /// </summary>
  public abstract void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext,
    string proofContext, bool allowAssumptionVariables, bool inConstructorInitializationPhase);
}