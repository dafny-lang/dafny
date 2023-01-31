
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Security.Policy;

namespace Microsoft.Dafny;

public abstract class Statement : RangeNode, IAttributeBearingDeclaration {
  public override IToken Tok => PostLabelToken ?? base.Tok;
  
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
  public static VarDeclStmt CreateLocalVariable(RangeToken tok, string name, Type type) {
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
  public static VarDeclStmt CreateLocalVariable(RangeToken rangeToken, string name, Expression value) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(value != null);
    var variable = new LocalVariable(rangeToken, name, value.Type, false);
    variable.type = value.Type;
    Expression variableExpr = new IdentifierExpr(rangeToken, variable);
    var variableUpdateStmt = new UpdateStmt(rangeToken, Util.Singleton(variableExpr),
      Util.Singleton<AssignmentRhs>(new ExprRhs(value)));
    var variableAssignStmt = new AssignStmt(rangeToken, variableUpdateStmt.Lhss[0], variableUpdateStmt.Rhss[0]);
    variableUpdateStmt.ResolvedStatements = new List<Statement>() { variableAssignStmt };
    return new VarDeclStmt(rangeToken, Util.Singleton(variable), variableUpdateStmt);
  }

  public static PrintStmt CreatePrintStmt(RangeToken tok, params Expression[] exprs) {
    return new PrintStmt(tok, exprs.ToList());
  }

  public override string ToString() {
    try {
      return Printer.StatementToString(this);
    } catch (Exception e) {
      return $"couldn't print stmt because: {e.Message}";
    }
  }

  public override IEnumerable<Node> Children =>
    (Attributes != null ? new List<Node> { Attributes } : Enumerable.Empty<Node>()).Concat(
      SubStatements.Concat<Node>(SubExpressions));
}

public class LList<T> {
  public readonly T Data;
  public readonly LList<T> Next;

  public LList(T d, LList<T> next) {
    Data = d;
    Next = next;
  }

  public static LList<T> Append(LList<T> a, LList<T> b) {
    if (a == null) {
      return b;
    }

    return new LList<T>(a.Data, Append(a.Next, b));
    // pretend this is ML
  }
  public static int Count(LList<T> n) {
    int count = 0;
    while (n != null) {
      count++;
      n = n.Next;
    }
    return count;
  }
}

public class Label {
  public readonly IToken Tok;
  public readonly string Name;
  string uniqueId = null;
  public string AssignUniqueId(FreshIdGenerator idGen) {
    if (uniqueId == null) {
      uniqueId = idGen.FreshNumericId("label");
    }
    return uniqueId;
  }
  public Label(IToken tok, string/*?*/ label) {
    Contract.Requires(tok != null);
    Tok = tok;
    Name = label;
  }
}

public class AssertLabel : Label {

  [FilledInDuringTranslation]
  public Boogie.Expr E;

  public AssertLabel(IToken tok, string label)
    : base(tok, label) {
    Contract.Requires(tok != null);
    Contract.Requires(label != null);
  }
}

public class RevealStmt : Statement, ICloneable<RevealStmt> {
  public readonly List<Expression> Exprs;
  [FilledInDuringResolution] public readonly List<AssertLabel> LabeledAsserts = new List<AssertLabel>();  // to indicate that "Expr" denotes a labeled assertion
  [FilledInDuringResolution] public readonly List<Statement> ResolvedStatements = new List<Statement>();

  public override IEnumerable<Statement> SubStatements {
    get { return ResolvedStatements; }
  }

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Exprs != null);
    Contract.Invariant(LabeledAsserts.Count <= Exprs.Count);
  }

  public RevealStmt Clone(Cloner cloner) {
    return new RevealStmt(cloner, this);
  }

  public RevealStmt(Cloner cloner, RevealStmt original) : base(cloner, original) {
    Exprs = original.Exprs.Select(cloner.CloneExpr).ToList();
    if (cloner.CloneResolvedFields) {
      LabeledAsserts = original.LabeledAsserts.Select(a => new AssertLabel(cloner.Tok(a.Tok), a.Name)).ToList();
      ResolvedStatements = original.ResolvedStatements.Select(cloner.CloneStmt).ToList();
    }
  }

  public RevealStmt(RangeToken rangeToken, List<Expression> exprs)
    : base(rangeToken) {
    Contract.Requires(exprs != null);
    this.Exprs = exprs;
  }

  public static string SingleName(Expression e) {
    Contract.Requires(e != null);
    if (e is NameSegment || e is LiteralExpr) {
      return e.tok.val;
    } else {
      return null;
    }
  }
}

public abstract class ProduceStmt : Statement {
  public List<AssignmentRhs> Rhss;
  [FilledInDuringResolution]
  public UpdateStmt HiddenUpdate;

  protected ProduceStmt(Cloner cloner, ProduceStmt original) : base(cloner, original) {
    if (original.Rhss != null) {
      Rhss = original.Rhss.Select(cloner.CloneRHS).ToList();
    }
    if (cloner.CloneResolvedFields) {
      if (original.HiddenUpdate != null) {
        HiddenUpdate = new UpdateStmt(cloner, original.HiddenUpdate);
      }
    }
  }

  public ProduceStmt(RangeToken rangeToken, List<AssignmentRhs> rhss)
    : base(rangeToken) {
    this.Rhss = rhss;
    HiddenUpdate = null;
  }

  public override IEnumerable<Node> Children =>
    HiddenUpdate == null ? base.Children : new Node[] { HiddenUpdate }.Concat(base.Children);

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      foreach (var rhs in Rhss ?? Enumerable.Empty<AssignmentRhs>()) {
        foreach (var e in rhs.NonSpecificationSubExpressions) {
          yield return e;
        }
      }
    }
  }
  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      foreach (var rhs in Rhss ?? Enumerable.Empty<AssignmentRhs>()) {
        foreach (var e in rhs.SpecificationSubExpressions) {
          yield return e;
        }
      }
    }
  }
  public override IEnumerable<Statement> SubStatements {
    get {
      foreach (var rhs in Rhss ?? Enumerable.Empty<AssignmentRhs>()) {
        foreach (var s in rhs.SubStatements) {
          yield return s;
        }
      }
    }
  }
}

public class YieldStmt : ProduceStmt, ICloneable<YieldStmt> {
  public YieldStmt Clone(Cloner cloner) {
    return new YieldStmt(cloner, this);
  }

  public YieldStmt(Cloner cloner, YieldStmt original) : base(cloner, original) {
  }

  public YieldStmt(RangeToken rangeToken, List<AssignmentRhs> rhss)
    : base(rangeToken, rhss) {
  }
}

public abstract class AssignmentRhs : RangeNode, IAttributeBearingDeclaration {
  private Attributes attributes;
  public Attributes Attributes {
    get {
      return attributes;
    }
    set {
      attributes = value;
    }
  }

  public bool HasAttributes() {
    return Attributes != null;
  }

  internal AssignmentRhs(Cloner cloner, AssignmentRhs original) : base(cloner, original) {
    Attributes = cloner.CloneAttributes(original.Attributes);
  }

  internal AssignmentRhs(RangeToken tok, Attributes attrs = null) : base(tok) {
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
    get {
      yield break;
    }
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
  /// Returns the non-null sub-statements of the AssignmentRhs.
  /// </summary>
  public virtual IEnumerable<Statement> SubStatements {
    get { yield break; }
  }
}

public class ExprRhs : AssignmentRhs {
  public readonly Expression Expr;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Expr != null);
  }
  
  public ExprRhs(Expression expr, Attributes attrs = null)
    : base(new RangeToken(expr.StartToken, attrs?.EndToken ?? expr.EndToken), attrs) {
    Contract.Requires(expr != null);
    Expr = expr;
  }
  public override bool CanAffectPreviouslyKnownExpressions { get { return false; } }
  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      yield return Expr;
    }
  }

  public override IEnumerable<Node> Children => new[] { Expr };
}

/// <summary>
/// A TypeRhs represents one of five things, each having to do with allocating something in the heap:
///  * new T[EE]
///    This allocates an array of objects of type T (where EE is a list of expression)
///  * new T[EE] (elementInit)
///    This is like the previous, but uses "elementInit" to initialize the elements of the new array.
///  * new T[E] [EE]
///    This is like the first one, but uses the elements displayed in the list EE as the initial
///    elements of the array.  Only a 1-dimensional array may be used in this case.  The size denoted
///    by E must equal the length of EE.
///  * new C
///    This allocates an object of type C
///  * new C.Init(EE)
///    This allocates an object of type C and then invokes the method/constructor Init on it
/// There are three ways to construct a TypeRhs syntactically:
///  * TypeRhs(T, EE, initExpr)
///      -- represents "new T[EE]" (with "elementInit" being "null") and "new T[EE] (elementInit)"
///  * TypeRhs(T, E, EE)
///      -- represents "new T[E] [EE]"
///  * TypeRhs(C)
///      -- represents new C
///  * TypeRhs(Path, EE)
///    Here, Path may either be of the form C.Init
///      -- represents new C.Init(EE)
///    or all of Path denotes a type
///      -- represents new C._ctor(EE), where _ctor is the anonymous constructor for class C
/// </summary>
public class TypeRhs : AssignmentRhs, ICloneable<TypeRhs> {
  /// <summary>
  /// If ArrayDimensions != null, then the TypeRhs represents "new EType[ArrayDimensions]",
  ///     ElementInit is non-null to represent "new EType[ArrayDimensions] (elementInit)",
  ///     InitDisplay is non-null to represent "new EType[ArrayDimensions] [InitDisplay]",
  ///     and Arguments, Path, and InitCall are all null.
  /// If ArrayDimentions == null && Arguments == null, then the TypeRhs represents "new EType"
  ///     and ElementInit, Path, and InitCall are all null.
  /// If Arguments != null, then the TypeRhs represents "new Path(Arguments)"
  ///     and EType and InitCall is filled in by resolution, and ArrayDimensions == null and ElementInit == null.
  /// If OptionalNameComponent == null and Arguments != null, then the TypeRHS has not been resolved yet;
  ///   resolution will either produce an error or will chop off the last part of "EType" and move it to
  ///   OptionalNameComponent, after which the case above applies.
  /// </summary>
  [FilledInDuringResolution] public Type EType;  // in the case of Arguments != null
  public readonly List<Expression> ArrayDimensions;
  public readonly Expression ElementInit;
  public readonly List<Expression> InitDisplay;
  public readonly ActualBindings/*?*/ Bindings;
  public List<Expression> Arguments {
    get {
      Contract.Requires(Bindings != null);
      return Bindings.Arguments;
    }
  }

  public TypeRhs Clone(Cloner cloner) {
    return new TypeRhs(cloner, this);
  }

  public TypeRhs(Cloner cloner, TypeRhs original)
    : base(cloner, original) {
    EType = cloner.CloneType(original.EType);
    if (original.ArrayDimensions != null) {
      if (original.InitDisplay != null) {
        Contract.Assert(original.ArrayDimensions.Count == 1);
        ArrayDimensions = new List<Expression> { cloner.CloneExpr(original.ArrayDimensions[0]) };
        InitDisplay = original.InitDisplay.ConvertAll(cloner.CloneExpr);
      } else {
        ArrayDimensions = original.ArrayDimensions.Select(cloner.CloneExpr).ToList();
        ElementInit = cloner.CloneExpr(original.ElementInit);
      }
    } else if (original.Bindings == null) {
    } else {
      Path = cloner.CloneType(original.Path);
      Bindings = new ActualBindings(cloner, original.Bindings);
    }

    if (cloner.CloneResolvedFields) {
      InitCall = cloner.CloneStmt(original.InitCall) as CallStmt;
      Type = cloner.CloneType(original.Type);
    }
  }

  public Type Path;
  [FilledInDuringResolution] public CallStmt InitCall;  // may be null (and is definitely null for arrays),
  [FilledInDuringResolution] public Type Type;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(EType != null || Bindings != null);
    Contract.Invariant(ElementInit == null || InitDisplay == null);
    Contract.Invariant(InitDisplay == null || ArrayDimensions.Count == 1);
    Contract.Invariant(ArrayDimensions == null || (Bindings == null && Path == null && InitCall == null && 1 <= ArrayDimensions.Count));
    Contract.Invariant(Bindings == null || (Path != null && ArrayDimensions == null && ElementInit == null && InitDisplay == null));
    Contract.Invariant(!(ArrayDimensions == null && Bindings == null) || (Path == null && InitCall == null && ElementInit == null && InitDisplay == null));
  }

  public TypeRhs(RangeToken tok, Type type, List<Expression> arrayDimensions, Expression elementInit)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(type != null);
    Contract.Requires(arrayDimensions != null && 1 <= arrayDimensions.Count);
    EType = type;
    ArrayDimensions = arrayDimensions;
    ElementInit = elementInit;
  }
  public TypeRhs(RangeToken tok, Type type, Expression dim, List<Expression> initDisplay)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(type != null);
    Contract.Requires(dim != null);
    Contract.Requires(initDisplay != null);
    EType = type;
    ArrayDimensions = new List<Expression> { dim };
    InitDisplay = initDisplay;
  }
  public TypeRhs(RangeToken tok, Type type)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(type != null);
    EType = type;
  }
  public TypeRhs(RangeToken tok, Type path, List<ActualBinding> arguments)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(path != null);
    Contract.Requires(arguments != null);
    Path = path;
    Bindings = new ActualBindings(arguments);
  }
  public override bool CanAffectPreviouslyKnownExpressions {
    get {
      if (InitCall != null) {
        foreach (var mod in InitCall.Method.Mod.Expressions) {
          if (!(mod.E is ThisExpr)) {
            return true;
          }
        }
      }
      return false;
    }
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      if (ArrayDimensions != null) {
        foreach (var e in ArrayDimensions) {
          yield return e;
        }
        if (ElementInit != null) {
          yield return ElementInit;
        }
        if (InitDisplay != null) {
          foreach (var e in InitDisplay) {
            yield return e;
          }
        }
      }
    }
  }
  public override IEnumerable<Statement> SubStatements {
    get {
      if (InitCall != null) {
        yield return InitCall;
      }
    }
  }

  public IToken Start => Tok;
  public override IEnumerable<Node> Children {
    get {
      if (ArrayDimensions == null) {
        if (InitCall != null) {
          return new[] { InitCall };
        }

        return EType.Nodes;
      }

      return EType.Nodes.Concat(SubExpressions).Concat<Node>(SubStatements);
    }
  }
}

public class HavocRhs : AssignmentRhs {
  public HavocRhs(RangeToken tok)
    : base(tok) {
  }
  public override bool CanAffectPreviouslyKnownExpressions { get { return false; } }
  public override IEnumerable<Node> Children => Enumerable.Empty<Node>();
}

public class VarDeclStmt : Statement, ICloneable<VarDeclStmt> {
  public readonly List<LocalVariable> Locals;
  public readonly ConcreteUpdateStatement Update;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Locals));
    Contract.Invariant(Locals.Count != 0);
  }

  public VarDeclStmt Clone(Cloner cloner) {
    return new VarDeclStmt(cloner, this);
  }

  public VarDeclStmt(Cloner cloner, VarDeclStmt original) : base(cloner, original) {
    Locals = original.Locals.Select(l => cloner.CloneLocalVariable(l, false)).ToList();
    Update = (ConcreteUpdateStatement)cloner.CloneStmt(original.Update);
  }

  public VarDeclStmt(RangeToken rangeToken, List<LocalVariable> locals, ConcreteUpdateStatement update)
    : base(rangeToken) {
    Contract.Requires(locals != null);
    Contract.Requires(locals.Count != 0);

    Locals = locals;
    Update = update;
  }

  public override IEnumerable<Statement> SubStatements {
    get { if (Update != null) { yield return Update; } }
  }

  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      foreach (var v in Locals) {
        foreach (var e in Attributes.SubExpressions(v.Attributes)) {
          yield return e;
        }
      }
    }
  }

  public override IEnumerable<Node> Children => Locals.Concat<Node>(SubStatements);
}

public class VarDeclPattern : Statement, ICloneable<VarDeclPattern> {
  public readonly CasePattern<LocalVariable> LHS;
  public readonly Expression RHS;
  public bool HasGhostModifier;

  public VarDeclPattern Clone(Cloner cloner) {
    return new VarDeclPattern(cloner, this);
  }

  public VarDeclPattern(Cloner cloner, VarDeclPattern original) : base(cloner, original) {
    LHS = cloner.CloneCasePattern(original.LHS);
    RHS = cloner.CloneExpr(original.RHS);
    HasGhostModifier = original.HasGhostModifier;
  }

  public VarDeclPattern(RangeToken rangeToken, CasePattern<LocalVariable> lhs, Expression rhs, bool hasGhostModifier)
    : base(rangeToken) {
    LHS = lhs;
    RHS = rhs;
    HasGhostModifier = hasGhostModifier;
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) {
        yield return e;
      }
      yield return RHS;
    }
  }

  public override IEnumerable<Node> Children =>
    new List<Node> { LHS }.Concat(base.Children);

  public IEnumerable<LocalVariable> LocalVars {
    get {
      foreach (var bv in LHS.Vars) {
        yield return bv;
      }
    }
  }
}

/// <summary>
/// Common superclass of UpdateStmt, AssignSuchThatStmt and AssignOrReturnStmt
/// </summary>
public abstract class ConcreteUpdateStatement : Statement {
  public readonly List<Expression> Lhss;

  protected ConcreteUpdateStatement(Cloner cloner, ConcreteUpdateStatement original) : base(cloner, original) {
    Lhss = original.Lhss.Select(cloner.CloneExpr).ToList();
  }

  public ConcreteUpdateStatement(RangeToken rangeToken, List<Expression> lhss, Attributes attrs = null)
    : base(rangeToken, attrs) {
    Contract.Requires(cce.NonNullElements(lhss));
    Lhss = lhss;
  }
}

/// <summary>
/// Attributed tokens are used when a subpart of a statement or expression can take attributes.
/// (Perhaps in addition to attributes placed on the token itself.)
///
/// It is used in particular to attach `{:axiom}` tokens to the `assume` keyword
/// on the RHS of `:|` and `:-` (in contrast, for `assume` statements, the
/// `{:axiom}` attribute is directly attached to the statement-level
/// attributes).
/// </summary>
public record AttributedToken(IToken Token, Attributes Attrs) : IAttributeBearingDeclaration {
  Attributes IAttributeBearingDeclaration.Attributes => Attrs;
}

public class UpdateStmt : ConcreteUpdateStatement, ICloneable<UpdateStmt> {
  public readonly List<AssignmentRhs> Rhss;
  public readonly bool CanMutateKnownState;
  public Expression OriginalInitialLhs = null;

  public override IToken Tok {
    get {
      var firstRhs = Rhss.First();
      if (firstRhs.StartToken != StartToken) {
        // If there is an operator, use it as a token
        return firstRhs.StartToken.Prev;
      }

      return firstRhs.Tok;
    }
  }

  [FilledInDuringResolution] public List<Statement> ResolvedStatements;
  public override IEnumerable<Statement> SubStatements => Children.OfType<Statement>();

  public override IEnumerable<Node> Children => ResolvedStatements ?? Lhss.Concat<Node>(Rhss);

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Lhss));
    Contract.Invariant(cce.NonNullElements(Rhss));
  }

  public UpdateStmt Clone(Cloner cloner) {
    return new UpdateStmt(cloner, this);
  }

  public UpdateStmt(Cloner cloner, UpdateStmt original) : base(cloner, original) {
    Rhss = original.Rhss.Select(cloner.CloneRHS).ToList();
    CanMutateKnownState = original.CanMutateKnownState;
    if (cloner.CloneResolvedFields) {
      ResolvedStatements = original.ResolvedStatements.Select(cloner.CloneStmt).ToList();
    }
  }

  public UpdateStmt(RangeToken rangeToken, List<Expression> lhss, List<AssignmentRhs> rhss)
    : base(rangeToken, lhss) {
    Contract.Requires(cce.NonNullElements(lhss));
    Contract.Requires(cce.NonNullElements(rhss));
    Contract.Requires(lhss.Count != 0 || rhss.Count == 1);
    Rhss = rhss;
    CanMutateKnownState = false;
  }
  public UpdateStmt(RangeToken rangeToken, List<Expression> lhss, List<AssignmentRhs> rhss, bool mutate)
    : base(rangeToken, lhss) {
    Contract.Requires(cce.NonNullElements(lhss));
    Contract.Requires(cce.NonNullElements(rhss));
    Contract.Requires(lhss.Count != 0 || rhss.Count == 1);
    Rhss = rhss;
    CanMutateKnownState = mutate;
  }
}

public class LocalVariable : RangeNode, IVariable, IAttributeBearingDeclaration {
  public Name NameNode { get; set; }
  
  public Attributes Attributes;
  Attributes IAttributeBearingDeclaration.Attributes => Attributes;
  public bool IsGhost;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(NameNode != null);
    Contract.Invariant(OptionalType != null);
  }

  public override IToken Tok => RangeToken.StartToken;

  public LocalVariable(Cloner cloner, LocalVariable original)
    : base(cloner, original) {
    NameNode = original.NameNode.Clone(cloner);
    OptionalType = cloner.CloneType(original.OptionalType);
    IsGhost = original.IsGhost;

    if (cloner.CloneResolvedFields) {
      type = original.type;
    }
  }

  public LocalVariable(RangeToken rangeToken, Name nameNode, Type type, bool isGhost)
    : base(rangeToken) {
    Contract.Requires(nameNode != null);
    Contract.Requires(type != null);  // can be a proxy, though

    this.NameNode = nameNode;
    this.OptionalType = type;
    if (type is InferredTypeProxy) {
      ((InferredTypeProxy)type).KeepConstraints = true;
    }
    this.IsGhost = isGhost;
  }

  public string Name {
    get {
      Contract.Ensures(Contract.Result<string>() != null);
      return NameNode.Value;
    }
  }
  public static bool HasWildcardName(IVariable v) {
    Contract.Requires(v != null);
    return v.Name.StartsWith("_v");
  }
  public static string DisplayNameHelper(IVariable v) {
    Contract.Requires(v != null);
    return HasWildcardName(v) ? "_" : v.Name;
  }
  public string DisplayName {
    get { return DisplayNameHelper(this); }
  }
  private string uniqueName;
  public string UniqueName => uniqueName;
  public bool HasBeenAssignedUniqueName => uniqueName != null;
  public string AssignUniqueName(FreshIdGenerator generator) {
    return uniqueName ??= generator.FreshId(Name + "#");
  }

  private string sanitizedName;
  public string SanitizedName =>
    sanitizedName ??= $"_{IVariable.CompileNameIdGenerator.FreshNumericId()}_{NonglobalVariable.SanitizeName(Name)}";

  string compileName;
  public string CompileName =>
    compileName ??= SanitizedName;

  public readonly Type OptionalType;  // this is the type mentioned in the declaration, if any
  Type IVariable.OptionalType { get { return this.OptionalType; } }

  [FilledInDuringResolution]
  internal Type type;  // this is the declared or inferred type of the variable; it is non-null after resolution (even if resolution fails)
  public Type Type {
    get {
      Contract.Ensures(Contract.Result<Type>() != null);

      Contract.Assume(type != null);  /* we assume object has been resolved */
      return type.Normalize();
    }
  }
  public bool IsMutable {
    get {
      return true;
    }
  }
  bool IVariable.IsGhost {
    get {
      return this.IsGhost;
    }
  }
  /// <summary>
  /// This method retrospectively makes the LocalVariable a ghost.  It is to be used only during resolution.
  /// </summary>
  public void MakeGhost() {
    this.IsGhost = true;
  }

  public IToken NameToken => RangeToken.StartToken;
  public bool IsTypeExplicit = false;
  public override IEnumerable<Node> Children =>
    (Attributes != null ? new List<Node> { Attributes } : Enumerable.Empty<Node>()).Concat(
      IsTypeExplicit ? new List<Node>() { type } : Enumerable.Empty<Node>());
}

public class GuardedAlternative : RangeNode, IAttributeBearingDeclaration {
  public readonly bool IsBindingGuard;
  public readonly Expression Guard;
  public readonly List<Statement> Body;
  public Attributes Attributes;
  public override IEnumerable<Node> Children => (Attributes != null ? new List<Node> { Attributes } : Enumerable.Empty<Node>()).Concat(new List<Node>() { Guard }).Concat<Node>(Body);
  Attributes IAttributeBearingDeclaration.Attributes => Attributes;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Tok != null);
    Contract.Invariant(Guard != null);
    Contract.Invariant(!IsBindingGuard || (Guard is ExistsExpr && ((ExistsExpr)Guard).Range == null));
    Contract.Invariant(Body != null);
  }
  public GuardedAlternative(RangeToken tok, bool isBindingGuard, Expression guard, List<Statement> body) : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(guard != null);
    Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
    Contract.Requires(body != null);
    this.IsBindingGuard = isBindingGuard;
    this.Guard = guard;
    this.Body = body;
    this.Attributes = null;
  }
  public GuardedAlternative(RangeToken tok, bool isBindingGuard, Expression guard, List<Statement> body, Attributes attrs) : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(guard != null);
    Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
    Contract.Requires(body != null);
    this.IsBindingGuard = isBindingGuard;
    this.Guard = guard;
    this.Body = body;
    this.Attributes = attrs;
  }
}

public class WhileStmt : OneBodyLoopStmt, ICloneable<WhileStmt> {
  public readonly Expression/*?*/ Guard;

  public class LoopBodySurrogate {
    public readonly List<IVariable> LocalLoopTargets;
    public readonly bool UsesHeap;

    public LoopBodySurrogate(List<IVariable> localLoopTargets, bool usesHeap) {
      LocalLoopTargets = localLoopTargets;
      UsesHeap = usesHeap;
    }
  }

  public WhileStmt Clone(Cloner cloner) {
    return new WhileStmt(cloner, this);
  }

  public WhileStmt(Cloner cloner, WhileStmt original) : base(cloner, original) {
    Guard = cloner.CloneExpr(original.Guard);
  }

  public WhileStmt(RangeToken rangeToken, Expression guard,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    BlockStmt body)
    : base(rangeToken, invariants, decreases, mod, body, null) {
    this.Guard = guard;
  }

  public WhileStmt(RangeToken rangeToken, Expression guard,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    BlockStmt body, Attributes attrs)
    : base(rangeToken, invariants, decreases, mod, body, attrs) {
    this.Guard = guard;
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      if (Guard != null) {
        yield return Guard;
      }
    }
  }
}

/// <summary>
/// This class is really just a WhileStmt, except that it serves the purpose of remembering if the object was created as the result of a refinement
/// merge.
/// </summary>
public class RefinedWhileStmt : WhileStmt {
  public RefinedWhileStmt(RangeToken rangeToken, Expression guard,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    BlockStmt body)
    : base(rangeToken, guard, invariants, decreases, mod, body) {
    Contract.Requires(body != null);
  }
}

/// <summary>
/// The class represents several possible scenarios:
/// * ...;
///   S == null
/// * assert ...
///   ConditionOmitted == true
/// * assume ...
///   ConditionOmitted == true
/// * if ... { Stmt }
///   if ... { Stmt } else ElseStmt
///   ConditionOmitted == true
/// * while ... invariant J;
///   ConditionOmitted == true && BodyOmitted == true
/// * while ... invariant J; { Stmt }
///   ConditionOmitted == true && BodyOmitted == false
/// * modify ...;
///   ConditionOmitted == true && BodyOmitted == false
/// * modify ... { Stmt }
///   ConditionOmitted == true && BodyOmitted == false
/// </summary>
public class SkeletonStatement : Statement, ICloneable<SkeletonStatement> {
  public readonly Statement S;
  public bool ConditionOmitted { get { return ConditionEllipsis != null; } }
  public readonly IToken ConditionEllipsis;
  public bool BodyOmitted { get { return BodyEllipsis != null; } }
  public readonly IToken BodyEllipsis;

  public SkeletonStatement Clone(Cloner cloner) {
    return new SkeletonStatement(cloner, this);
  }

  public SkeletonStatement(Cloner cloner, SkeletonStatement original) : base(cloner, original) {
    S = original.S == null ? null : cloner.CloneStmt(original.S);
    ConditionEllipsis = original.ConditionEllipsis;
    BodyEllipsis = original.BodyEllipsis;
  }

  public SkeletonStatement(RangeToken rangeToken)
    : base(rangeToken) {
    Contract.Requires(rangeToken != null);
    S = null;
  }
  public SkeletonStatement(Statement s, IToken conditionEllipsis, IToken bodyEllipsis)
    : base(s.RangeToken) {
    Contract.Requires(s != null);
    S = s;
    ConditionEllipsis = conditionEllipsis;
    BodyEllipsis = bodyEllipsis;
  }
  public override IEnumerable<Statement> SubStatements {
    get {
      // The SkeletonStatement is really a modification of its inner statement S.  Therefore,
      // we don't consider S to be a substatement.  Instead, the substatements of S are the
      // substatements of the SkeletonStatement.  In the case the SkeletonStatement modifies
      // S by omitting its body (which is true only for loops), there are no substatements.
      if (!BodyOmitted && S.SubStatements != null) {
        foreach (var s in S.SubStatements) {
          yield return s;
        }
      }
    }
  }
}

/// <summary>
/// A statement something like a try/catch block that recovers from halting.
/// Not actually useable in Dafny syntax, but would likely look something like this if it was:
///
/// try {
///   <Body>
/// } recover (haltMessage: string) {
///   <RecoveryBlock>
/// }
///
/// </summary>
public class TryRecoverStatement : Statement, ICloneable<TryRecoverStatement> {
  public readonly Statement TryBody;
  public readonly IVariable HaltMessageVar;
  public readonly Statement RecoverBody;

  public TryRecoverStatement Clone(Cloner cloner) {
    return new TryRecoverStatement(cloner, this);
  }

  public TryRecoverStatement(Cloner cloner, TryRecoverStatement original) : base(cloner, original) {
    TryBody = cloner.CloneStmt(original.TryBody);
    RecoverBody = cloner.CloneStmt(original.RecoverBody);
    HaltMessageVar = cloner.CloneIVariable(original.HaltMessageVar, false);
  }

  public TryRecoverStatement(Statement tryBody, IVariable haltMessageVar, Statement recoverBody)
    : base(new RangeToken(tryBody.StartToken, recoverBody.EndToken)) {
    Contract.Requires(tryBody != null);
    Contract.Requires(haltMessageVar != null);
    Contract.Requires(recoverBody != null);
    TryBody = tryBody;
    HaltMessageVar = haltMessageVar;
    RecoverBody = recoverBody;
  }
}
