using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Drawing.Imaging;
using System.Linq;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

public abstract class Statement : INode, IAttributeBearingDeclaration {
  public IToken EndTok { get; set; }  // typically a terminating semi-colon or end-curly-brace
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
    Contract.Invariant(EndTok != null);
  }

  [FilledInDuringResolution] public bool IsGhost;

  public Statement(IToken tok, IToken endTok, Attributes attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    this.Tok = tok;
    this.EndTok = endTok;
    this.RangeToken = new RangeToken(tok, endTok);
    this.attributes = attrs;
  }

  public Statement(IToken tok, IToken endTok)
    : this(tok, endTok, null) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
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
  /// Filters all sub expressions that are not part of specifications
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
      yield break;
    }
  }

  /// <summary>
  /// Returns the non-null expressions of this statement proper (that is, do not include the expressions of substatements).
  /// Filters all sub expressions that are not part of specifications
  /// </summary>
  public virtual IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in Attributes.SubExpressions(Attributes)) {
        yield return e;
      }
    }
  }

  /// <summary>
  /// Create a resolved statement for an uninitialized local variable.
  /// </summary>
  public static VarDeclStmt CreateLocalVariable(IToken tok, string name, Type type) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Contract.Requires(type != null);
    var variable = new LocalVariable(tok, tok, name, type, false);
    variable.type = type;
    return new VarDeclStmt(tok, tok, Util.Singleton(variable), null);
  }

  /// <summary>
  /// Create a resolved statement for a local variable with an initial value.
  /// </summary>
  public static VarDeclStmt CreateLocalVariable(IToken tok, string name, Expression value) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Contract.Requires(value != null);
    var variable = new LocalVariable(tok, tok, name, value.Type, false);
    variable.type = value.Type;
    Expression variableExpr = new IdentifierExpr(tok, variable);
    var variableUpdateStmt = new UpdateStmt(tok, tok, Util.Singleton(variableExpr),
      Util.Singleton<AssignmentRhs>(new ExprRhs(value)));
    var variableAssignStmt = new AssignStmt(tok, tok, variableUpdateStmt.Lhss[0], variableUpdateStmt.Rhss[0]);
    variableUpdateStmt.ResolvedStatements.Add(variableAssignStmt);
    return new VarDeclStmt(tok, tok, Util.Singleton(variable), variableUpdateStmt);
  }

  public static PrintStmt CreatePrintStmt(IToken tok, params Expression[] exprs) {
    return new PrintStmt(tok, tok, exprs.ToList());
  }

  public override IEnumerable<INode> Children =>
    (Attributes != null ? new List<INode> { Attributes } : Enumerable.Empty<INode>()).Concat(
      SubStatements.Concat<INode>(SubExpressions));

  public override IEnumerable<INode> ConcreteChildren =>
    (Attributes != null ? new List<INode> { Attributes } : Enumerable.Empty<INode>()).Concat(
    PreResolveSubStatements).Concat(PreResolveSubExpressions);
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
  public Boogie.Expr E;  // filled in during translation
  public AssertLabel(IToken tok, string label)
    : base(tok, label) {
    Contract.Requires(tok != null);
    Contract.Requires(label != null);
  }
}

public class RevealStmt : Statement {
  public readonly List<Expression> Exprs;
  [FilledInDuringResolution] public readonly List<AssertLabel> LabeledAsserts = new List<AssertLabel>();  // to indicate that "Expr" denotes a labeled assertion
  [FilledInDuringResolution] public readonly List<Statement> ResolvedStatements = new List<Statement>();

  public override IEnumerable<Statement> SubStatements {
    get { return ResolvedStatements; }
  }

  public override IEnumerable<Statement> PreResolveSubStatements => Enumerable.Empty<Statement>();

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Exprs != null);
    Contract.Invariant(LabeledAsserts.Count <= Exprs.Count);
  }

  public RevealStmt(IToken tok, IToken endTok, List<Expression> exprs)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
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
  public UpdateStmt HiddenUpdate;
  public ProduceStmt(IToken tok, IToken endTok, List<AssignmentRhs> rhss)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    this.Rhss = rhss;
    HiddenUpdate = null;
  }
  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      if (Rhss != null) {
        foreach (var rhs in Rhss) {
          foreach (var ee in rhs.SubExpressions) {
            yield return ee;
          }
        }
      }
    }
  }
  public override IEnumerable<Statement> SubStatements {
    get {
      if (Rhss != null) {
        foreach (var rhs in Rhss) {
          foreach (var s in rhs.SubStatements) {
            yield return s;
          }
        }
      }
    }
  }

  public override IEnumerable<Statement> PreResolveSubStatements {
    get {
      if (Rhss != null) {
        foreach (var rhs in Rhss) {
          foreach (var s in rhs.PreResolveSubStatements) {
            yield return s;
          }
        }
      }
    }
  }
}

public class YieldStmt : ProduceStmt {
  public YieldStmt(IToken tok, IToken endTok, List<AssignmentRhs> rhss)
    : base(tok, endTok, rhss) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
  }
}

public abstract class AssignmentRhs : INode {
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

  internal AssignmentRhs(IToken tok, Attributes attrs = null) {
    Tok = tok;
    Attributes = attrs;
  }
  public abstract bool CanAffectPreviouslyKnownExpressions { get; }
  /// <summary>
  /// Returns the non-null subexpressions of the AssignmentRhs.
  /// </summary>
  public virtual IEnumerable<Expression> SubExpressions {
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
  /// Returns the non-null substatements of the AssignmentRhs.
  /// </summary>
  public virtual IEnumerable<Statement> SubStatements {
    get { yield break; }
  }

  public virtual IEnumerable<Statement> PreResolveSubStatements => SubStatements;
}

public class ExprRhs : AssignmentRhs {
  public readonly Expression Expr;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Expr != null);
  }

  public ExprRhs(Expression expr, Attributes attrs = null)  // TODO: these 'attrs' apparently aren't handled correctly in the Cloner, and perhaps not in various visitors either (for example, CheckIsCompilable should not go into attributes)
    : base(expr.tok, attrs) {
    Contract.Requires(expr != null);
    Expr = expr;
  }
  public override bool CanAffectPreviouslyKnownExpressions { get { return false; } }
  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return Expr;
    }
  }

  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      foreach (var expr in base.PreResolveSubExpressions) {
        yield return expr;
      }

      yield return Expr;
    }
  }

  public override IEnumerable<INode> Children => new[] { Expr };
  public override IEnumerable<INode> ConcreteChildren => PreResolveSubExpressions;
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
public class TypeRhs : AssignmentRhs {
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

  public TypeRhs(IToken tok, Type type, List<Expression> arrayDimensions, Expression elementInit)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(type != null);
    Contract.Requires(arrayDimensions != null && 1 <= arrayDimensions.Count);
    EType = type;
    ArrayDimensions = arrayDimensions;
    ElementInit = elementInit;
  }
  public TypeRhs(IToken tok, Type type, Expression dim, List<Expression> initDisplay)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(type != null);
    Contract.Requires(dim != null);
    Contract.Requires(initDisplay != null);
    EType = type;
    ArrayDimensions = new List<Expression> { dim };
    InitDisplay = initDisplay;
  }
  public TypeRhs(IToken tok, Type type)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(type != null);
    EType = type;
  }
  public TypeRhs(IToken tok, Type path, List<ActualBinding> arguments)
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

  public override IEnumerable<Expression> SubExpressions {
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

      if (Arguments != null) {
        foreach (var e in Arguments) {
          yield return e;
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

  public override IEnumerable<INode> Children =>
    new[] { EType, Type }.OfType<UserDefinedType>()
      .Concat<INode>(ArrayDimensions ?? Enumerable.Empty<INode>())
      .Concat<INode>(ElementInit != null ? new[] { ElementInit } : Enumerable.Empty<INode>())
      .Concat<INode>(InitDisplay ?? Enumerable.Empty<INode>())
      .Concat<INode>(Bindings != null ? Arguments : Enumerable.Empty<INode>());

  public override IEnumerable<Statement> PreResolveSubStatements => Enumerable.Empty<Statement>();

  public override IEnumerable<INode> ConcreteChildren => Children;
}

public class HavocRhs : AssignmentRhs {
  public HavocRhs(IToken tok)
    : base(tok) {
  }
  public override bool CanAffectPreviouslyKnownExpressions { get { return false; } }
  public override IEnumerable<INode> Children => Enumerable.Empty<INode>();
  public override IEnumerable<INode> ConcreteChildren => Enumerable.Empty<INode>();
}

public class VarDeclStmt : Statement {
  public readonly List<LocalVariable> Locals;
  public readonly ConcreteUpdateStatement Update;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Locals));
    Contract.Invariant(Locals.Count != 0);
  }

  public VarDeclStmt(IToken tok, IToken endTok, List<LocalVariable> locals, ConcreteUpdateStatement update)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(locals != null);
    Contract.Requires(locals.Count != 0);

    Locals = locals;
    Update = update;
  }

  public override IEnumerable<Statement> SubStatements {
    get { if (Update != null) { yield return Update; } }
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      foreach (var v in Locals) {
        foreach (var e in Attributes.SubExpressions(v.Attributes)) {
          yield return e;
        }
      }

      if (this.Update != null) {
        foreach (var e in this.Update.NonSpecificationSubExpressions) {
          yield return e;
        }
      }
    }
  }

  public override IEnumerable<INode> Children => Locals.Concat<INode>(SubStatements);

  public override IEnumerable<INode> ConcreteChildren => Children;
}

public class VarDeclPattern : Statement {
  public readonly CasePattern<LocalVariable> LHS;
  public readonly Expression RHS;
  public bool HasGhostModifier;

  public VarDeclPattern(IToken tok, IToken endTok, CasePattern<LocalVariable> lhs, Expression rhs, bool hasGhostModifier)
    : base(tok, endTok) {
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

  public override IEnumerable<INode> Children =>
    new List<INode> { LHS }.Concat(base.Children);

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
  public ConcreteUpdateStatement(IToken tok, IToken endTok, List<Expression> lhss, Attributes attrs = null)
    : base(tok, endTok, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(cce.NonNullElements(lhss));
    Lhss = lhss;
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) {
        yield return e;
      }

      foreach (var lhs in Lhss) {
        yield return lhs;
      }
    }
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
public record AttributedToken(IToken Token, Attributes Attrs) { }

public class UpdateStmt : ConcreteUpdateStatement {
  public readonly List<AssignmentRhs> Rhss;
  public readonly bool CanMutateKnownState;
  public Expression OriginalInitialLhs = null;

  [FilledInDuringResolution] public readonly List<Statement> ResolvedStatements = new List<Statement>();
  public override IEnumerable<Statement> SubStatements {
    get { return ResolvedStatements; }
  }

  // Both resolved and unresolved are required. Duplicate usages will be filtered out.
  public override IEnumerable<INode> Children => Lhss.Concat<INode>(Rhss).Concat(ResolvedStatements);
  public override IEnumerable<INode> ConcreteChildren => Lhss.Concat<INode>(Rhss);

  public override IEnumerable<Statement> PreResolveSubStatements => Enumerable.Empty<Statement>();


  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Lhss));
    Contract.Invariant(cce.NonNullElements(Rhss));
  }
  public UpdateStmt(IToken tok, IToken endTok, List<Expression> lhss, List<AssignmentRhs> rhss)
    : base(tok, endTok, lhss) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(cce.NonNullElements(lhss));
    Contract.Requires(cce.NonNullElements(rhss));
    Contract.Requires(lhss.Count != 0 || rhss.Count == 1);
    Rhss = rhss;
    CanMutateKnownState = false;
  }
  public UpdateStmt(IToken tok, IToken endTok, List<Expression> lhss, List<AssignmentRhs> rhss, bool mutate)
    : base(tok, endTok, lhss) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(cce.NonNullElements(lhss));
    Contract.Requires(cce.NonNullElements(rhss));
    Contract.Requires(lhss.Count != 0 || rhss.Count == 1);
    Rhss = rhss;
    CanMutateKnownState = mutate;
  }
  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      foreach (var e in base.PreResolveSubExpressions) {
        yield return e;
      }
      foreach (var rhs in Rhss) {
        foreach (var e in rhs.PreResolveSubExpressions) {
          yield return e;
        }
      }
    }
  }
}

public class LocalVariable : INode, IVariable, IAttributeBearingDeclaration {
  public readonly IToken EndTok;  // typically a terminating semi-colon or end-curly-brace
  readonly string name;
  public Attributes Attributes;
  Attributes IAttributeBearingDeclaration.Attributes => Attributes;
  public bool IsGhost;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(name != null);
    Contract.Invariant(OptionalType != null);
  }

  public LocalVariable(IToken tok, IToken endTok, string name, Type type, bool isGhost) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(name != null);
    Contract.Requires(type != null);  // can be a proxy, though

    this.Tok = tok;
    this.EndTok = endTok;
    this.name = name;
    this.OptionalType = type;
    if (type is InferredTypeProxy) {
      ((InferredTypeProxy)type).KeepConstraints = true;
    }
    this.IsGhost = isGhost;
  }

  public string Name {
    get {
      Contract.Ensures(Contract.Result<string>() != null);
      return name;
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
  IToken IVariable.Tok {
    get {
      return Tok;
    }
  }

  public IToken NameToken => Tok;
  public bool IsTypeExplicit = false;
  public override IEnumerable<INode> Children =>
    (Attributes != null ? new List<INode> { Attributes } : Enumerable.Empty<INode>()).Concat(
      IsTypeExplicit ? new List<INode>() { type } : Enumerable.Empty<INode>());

  public override IEnumerable<INode> ConcreteChildren =>
    (Attributes != null ? new List<INode> { Attributes } : Enumerable.Empty<INode>()).Concat(
      IsTypeExplicit ? new List<INode>() { OptionalType ?? type } : Enumerable.Empty<INode>());
}

public class GuardedAlternative : INode, IAttributeBearingDeclaration {
  public readonly bool IsBindingGuard;
  public readonly Expression Guard;
  public readonly List<Statement> Body;
  public Attributes Attributes;
  public override IEnumerable<INode> Children => (Attributes != null ? new List<INode> { Attributes } : Enumerable.Empty<INode>()).Concat(new List<INode>() { Guard }).Concat<INode>(Body);
  public override IEnumerable<INode> ConcreteChildren => Children;

  Attributes IAttributeBearingDeclaration.Attributes => Attributes;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Tok != null);
    Contract.Invariant(Guard != null);
    Contract.Invariant(!IsBindingGuard || (Guard is ExistsExpr && ((ExistsExpr)Guard).Range == null));
    Contract.Invariant(Body != null);
  }
  public GuardedAlternative(IToken tok, bool isBindingGuard, Expression guard, List<Statement> body) {
    Contract.Requires(tok != null);
    Contract.Requires(guard != null);
    Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
    Contract.Requires(body != null);
    this.Tok = tok;
    this.IsBindingGuard = isBindingGuard;
    this.Guard = guard;
    this.Body = body;
    this.Attributes = null;
  }
  public GuardedAlternative(IToken tok, bool isBindingGuard, Expression guard, List<Statement> body, Attributes attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(guard != null);
    Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
    Contract.Requires(body != null);
    this.Tok = tok;
    this.IsBindingGuard = isBindingGuard;
    this.Guard = guard;
    this.Body = body;
    this.Attributes = attrs;
  }
}

public class WhileStmt : OneBodyLoopStmt {
  public readonly Expression/*?*/ Guard;

  public class LoopBodySurrogate {
    public readonly List<IVariable> LocalLoopTargets;
    public readonly bool UsesHeap;

    public LoopBodySurrogate(List<IVariable> localLoopTargets, bool usesHeap) {
      LocalLoopTargets = localLoopTargets;
      UsesHeap = usesHeap;
    }
  }

  public WhileStmt(IToken tok, IToken endTok, Expression guard,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    BlockStmt body)
    : base(tok, endTok, invariants, decreases, mod, body, null) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    this.Guard = guard;
  }

  public WhileStmt(IToken tok, IToken endTok, Expression guard,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    BlockStmt body, Attributes attrs)
    : base(tok, endTok, invariants, decreases, mod, body, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    this.Guard = guard;
  }

  public override IEnumerable<Statement> SubStatements {
    get {
      if (Body != null) {
        yield return Body;
      }
    }
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
  public RefinedWhileStmt(IToken tok, IToken endTok, Expression guard,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    BlockStmt body)
    : base(tok, endTok, guard, invariants, decreases, mod, body) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
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
public class SkeletonStatement : Statement {
  public readonly Statement S;
  public bool ConditionOmitted { get { return ConditionEllipsis != null; } }
  public readonly IToken ConditionEllipsis;
  public bool BodyOmitted { get { return BodyEllipsis != null; } }
  public readonly IToken BodyEllipsis;
  public SkeletonStatement(IToken tok, IToken endTok)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    S = null;
  }
  public SkeletonStatement(Statement s, IToken conditionEllipsis, IToken bodyEllipsis)
    : base(s.Tok, s.EndTok) {
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

  public override IEnumerable<Statement> PreResolveSubStatements {
    get {
      yield return S;
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
public class TryRecoverStatement : Statement {
  public readonly Statement TryBody;
  public readonly IVariable HaltMessageVar;
  public readonly Statement RecoverBody;
  public TryRecoverStatement(Statement tryBody, IVariable haltMessageVar, Statement recoverBody)
    : base(tryBody.Tok, recoverBody.EndTok) {
    Contract.Requires(tryBody != null);
    Contract.Requires(haltMessageVar != null);
    Contract.Requires(recoverBody != null);
    TryBody = tryBody;
    HaltMessageVar = haltMessageVar;
    RecoverBody = recoverBody;
  }
}
