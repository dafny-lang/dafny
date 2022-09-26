
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Drawing.Imaging;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class Statement : IAttributeBearingDeclaration, INode {
  public readonly IToken Tok;
  public readonly IToken EndTok;  // typically a terminating semi-colon or end-curly-brace
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

  [FilledInDuringResolution] private IToken rangeToken;
  public virtual IToken RangeToken {
    get {
      if (rangeToken == null) {
        // Need a special case for the elephant operator to avoid end < start
        rangeToken = new RangeToken(Tok, Tok.pos > EndTok.pos ? Tok : EndTok);
      }
      return rangeToken;
    }
  }

  public virtual IEnumerable<INode> Children => SubStatements.Concat<INode>(SubExpressions);
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

public abstract class PredicateStmt : Statement {
  public readonly Expression Expr;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Expr != null);
  }

  public PredicateStmt(IToken tok, IToken endTok, Expression expr, Attributes attrs)
    : base(tok, endTok, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(expr != null);
    this.Expr = expr;
  }

  public PredicateStmt(IToken tok, IToken endTok, Expression expr)
    : this(tok, endTok, expr, null) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(expr != null);
    this.Expr = expr;
  }
}

public class AssertStmt : PredicateStmt {
  public readonly BlockStmt Proof;
  public readonly AssertLabel Label;
  public AssertStmt(IToken tok, IToken endTok, Expression expr, BlockStmt/*?*/ proof, AssertLabel/*?*/ label, Attributes attrs)
    : base(tok, endTok, expr, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(expr != null);
    Proof = proof;
    Label = label;
  }
  public override IEnumerable<Statement> SubStatements {
    get {
      if (Proof != null) {
        yield return Proof;
      }
    }
  }
  public void AddCustomizedErrorMessage(IToken tok, string s) {
    var args = new List<Expression>() { new StringLiteralExpr(tok, s, true) };
    IToken openBrace = tok;
    IToken closeBrace = new Token(tok.line, tok.col + 7 + s.Length + 1); // where 7 = length(":error ")
    this.Attributes = new UserSuppliedAttributes(tok, openBrace, closeBrace, args, this.Attributes);
  }

  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      yield return Expr;
    }
  }
}

public class ExpectStmt : PredicateStmt {
  public Expression Message;
  public ExpectStmt(IToken tok, IToken endTok, Expression expr, Expression message, Attributes attrs)
    : base(tok, endTok, expr, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(expr != null);
    this.Message = message;
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      yield return Expr;
      if (Message != null) {
        yield return Message;
      }
    }
  }
}

public class AssumeStmt : PredicateStmt {
  public AssumeStmt(IToken tok, IToken endTok, Expression expr, Attributes attrs)
    : base(tok, endTok, expr, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(expr != null);
  }
  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      yield return Expr;
    }
  }
}

public class PrintStmt : Statement {
  public readonly List<Expression> Args;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Args));
  }

  public PrintStmt(IToken tok, IToken endTok, List<Expression> args)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(cce.NonNullElements(args));

    Args = args;
  }
  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      foreach (var arg in Args) {
        yield return arg;
      }
    }
  }
}

public class RevealStmt : Statement {
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

/// <summary>
/// Class "BreakStmt" represents both "break" and "continue" statements.
/// </summary>
public class BreakStmt : Statement, IHasUsages {
  public readonly IToken TargetLabel;
  public readonly bool IsContinue;
  public string Kind => IsContinue ? "continue" : "break";
  public readonly int BreakAndContinueCount;
  [FilledInDuringResolution] public Statement TargetStmt;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(TargetLabel != null || 1 <= BreakAndContinueCount);
  }

  public BreakStmt(IToken tok, IToken endTok, IToken targetLabel, bool isContinue)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(targetLabel != null);
    this.TargetLabel = targetLabel;
    this.IsContinue = isContinue;
  }

  /// <summary>
  /// For "isContinue == false", represents the statement "break ^breakAndContinueCount ;".
  /// For "isContinue == true", represents the statement "break ^(breakAndContinueCount - 1) continue;".
  /// </summary>
  public BreakStmt(IToken tok, IToken endTok, int breakAndContinueCount, bool isContinue)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(1 <= breakAndContinueCount);
    this.BreakAndContinueCount = breakAndContinueCount;
    this.IsContinue = isContinue;
  }

  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations() {
    return new[] { TargetStmt }.OfType<IDeclarationOrUsage>();
  }

  public IToken NameToken => Tok;
}

public abstract class ProduceStmt : Statement {
  public List<AssignmentRhs> rhss;
  public UpdateStmt hiddenUpdate;
  public ProduceStmt(IToken tok, IToken endTok, List<AssignmentRhs> rhss)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    this.rhss = rhss;
    hiddenUpdate = null;
  }
  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      if (rhss != null) {
        foreach (var rhs in rhss) {
          foreach (var ee in rhs.SubExpressions) {
            yield return ee;
          }
        }
      }
    }
  }
  public override IEnumerable<Statement> SubStatements {
    get {
      if (rhss != null) {
        foreach (var rhs in rhss) {
          foreach (var s in rhs.SubStatements) {
            yield return s;
          }
        }
      }
    }
  }
}

public class ReturnStmt : ProduceStmt {
  public bool ReverifyPost;  // set during pre-resolution refinement transformation
  public ReturnStmt(IToken tok, IToken endTok, List<AssignmentRhs> rhss)
    : base(tok, endTok, rhss) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
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
  public readonly IToken Tok;

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
  /// Returns the non-null sub-statements of the AssignmentRhs.
  /// </summary>
  public virtual IEnumerable<Statement> SubStatements {
    get { yield break; }
  }

  public abstract IEnumerable<INode> Children { get; }
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

  public override IEnumerable<INode> Children => new[] { Expr };
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
public class TypeRhs : AssignmentRhs, INode {
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
  public override IEnumerable<INode> Children => new[] { EType, Type }.OfType<UserDefinedType>();
}

public class HavocRhs : AssignmentRhs {
  public HavocRhs(IToken tok)
    : base(tok) {
  }
  public override bool CanAffectPreviouslyKnownExpressions { get { return false; } }
  public override IEnumerable<INode> Children => Enumerable.Empty<INode>();
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
    }
  }

  public override IEnumerable<INode> Children => Locals.Concat<INode>(SubStatements);
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
}

public class AssignSuchThatStmt : ConcreteUpdateStatement {
  public readonly Expression Expr;
  public readonly IToken AssumeToken;

  [FilledInDuringResolution] public List<ComprehensionExpr.BoundedPool> Bounds;  // null for a ghost statement
  // invariant Bounds == null || Bounds.Count == BoundVars.Count;
  [FilledInDuringResolution] public List<IVariable> MissingBounds;  // remains "null" if bounds can be found
  // invariant Bounds == null || MissingBounds == null;
  public class WiggleWaggleBound : ComprehensionExpr.BoundedPool {
    public override PoolVirtues Virtues => PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
    public override int Preference() => 1;
  }

  public override IEnumerable<INode> Children => Lhss.Concat<INode>(new[] { Expr });

  /// <summary>
  /// "assumeToken" is allowed to be "null", in which case the verifier will check that a RHS value exists.
  /// If "assumeToken" is non-null, then it should denote the "assume" keyword used in the statement.
  /// </summary>
  public AssignSuchThatStmt(IToken tok, IToken endTok, List<Expression> lhss, Expression expr, IToken assumeToken, Attributes attrs)
    : base(tok, endTok, lhss, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(cce.NonNullElements(lhss));
    Contract.Requires(lhss.Count != 0);
    Contract.Requires(expr != null);
    Expr = expr;
    if (assumeToken != null) {
      AssumeToken = assumeToken;
    }
  }
  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      yield return Expr;
      foreach (var lhs in Lhss) {
        yield return lhs;
      }
    }
  }
}

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
}

public class AssignOrReturnStmt : ConcreteUpdateStatement {
  public readonly Expression Rhs; // this is the unresolved RHS, and thus can also be a method call
  public readonly List<AssignmentRhs> Rhss;
  public readonly IToken KeywordToken;
  [FilledInDuringResolution] public readonly List<Statement> ResolvedStatements = new List<Statement>();
  public override IEnumerable<Statement> SubStatements {
    get { return ResolvedStatements; }
  }

  public override IEnumerable<INode> Children => ResolvedStatements;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Lhss != null);
    Contract.Invariant(
      Lhss.Count == 0 ||                   // ":- MethodOrExpresion;" which returns void success or an error
      (Lhss.Count == 1 && Lhss[0] != null)   // "y :- MethodOrExpression;"
    );
    Contract.Invariant(Rhs != null);
  }

  public AssignOrReturnStmt(IToken tok, IToken endTok, List<Expression> lhss, Expression rhs, IToken keywordToken, List<AssignmentRhs> rhss = null)
    : base(tok, endTok, lhss) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(lhss != null);
    Contract.Requires(lhss.Count <= 1);
    Contract.Requires(rhs != null);
    Rhs = rhs;
    Rhss = rhss;
    KeywordToken = keywordToken;
  }
}

public class AssignStmt : Statement {
  public readonly Expression Lhs;
  public readonly AssignmentRhs Rhs;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Lhs != null);
    Contract.Invariant(Rhs != null);
  }

  public AssignStmt(IToken tok, IToken endTok, Expression lhs, AssignmentRhs rhs)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(lhs != null);
    Contract.Requires(rhs != null);
    this.Lhs = lhs;
    this.Rhs = rhs;
  }

  public override IEnumerable<Statement> SubStatements {
    get {
      foreach (var s in Rhs.SubStatements) {
        yield return s;
      }
    }
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      yield return Lhs;
      foreach (var ee in Rhs.SubExpressions) {
        yield return ee;
      }
    }
  }

  /// <summary>
  /// This method assumes "lhs" has been successfully resolved.
  /// </summary>
  public static bool LhsIsToGhost(Expression lhs) {
    Contract.Requires(lhs != null);
    return LhsIsToGhost_Which(lhs) == NonGhostKind.IsGhost;
  }
  public static bool LhsIsToGhostOrAutoGhost(Expression lhs) {
    Contract.Requires(lhs != null);
    return LhsIsToGhost_Which(lhs) == NonGhostKind.IsGhost || lhs.Resolved is AutoGhostIdentifierExpr;
  }
  public enum NonGhostKind { IsGhost, Variable, Field, ArrayElement }
  public static string NonGhostKind_To_String(NonGhostKind gk) {
    Contract.Requires(gk != NonGhostKind.IsGhost);
    switch (gk) {
      case NonGhostKind.Variable: return "non-ghost variable";
      case NonGhostKind.Field: return "non-ghost field";
      case NonGhostKind.ArrayElement: return "array element";
      default:
        Contract.Assume(false);  // unexpected NonGhostKind
        throw new cce.UnreachableException();  // please compiler
    }
  }
  /// <summary>
  /// This method assumes "lhs" has been successfully resolved.
  /// </summary>
  public static NonGhostKind LhsIsToGhost_Which(Expression lhs) {
    Contract.Requires(lhs != null);
    lhs = lhs.Resolved;
    if (lhs is AutoGhostIdentifierExpr) {
      // TODO: Should we return something different for this case?
      var x = (IdentifierExpr)lhs;
      if (!x.Var.IsGhost) {
        return NonGhostKind.Variable;
      }
    } else if (lhs is IdentifierExpr) {
      var x = (IdentifierExpr)lhs;
      if (!x.Var.IsGhost) {
        return NonGhostKind.Variable;
      }
    } else if (lhs is MemberSelectExpr) {
      var x = (MemberSelectExpr)lhs;
      if (!x.Member.IsGhost) {
        return NonGhostKind.Field;
      }
    } else {
      // LHS denotes an array element, which is always non-ghost
      return NonGhostKind.ArrayElement;
    }
    return NonGhostKind.IsGhost;
  }
}

public class LocalVariable : IVariable, IAttributeBearingDeclaration {
  public readonly IToken Tok;
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
  public IEnumerable<INode> Children => type.Nodes;
}

/// <summary>
/// A CallStmt is always resolved.  It is typically produced as a resolved counterpart of the syntactic AST note ApplySuffix.
/// </summary>
public class CallStmt : Statement {
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(MethodSelect.Member is Method);
    Contract.Invariant(cce.NonNullElements(Lhs));
    Contract.Invariant(cce.NonNullElements(Args));
  }

  public readonly List<Expression> Lhs;
  public readonly MemberSelectExpr MethodSelect;
  public readonly ActualBindings Bindings;
  public List<Expression> Args => Bindings.Arguments;
  public Expression OriginalInitialLhs = null;

  public Expression Receiver { get { return MethodSelect.Obj; } }
  public Method Method { get { return (Method)MethodSelect.Member; } }

  public CallStmt(IToken tok, IToken endTok, List<Expression> lhs, MemberSelectExpr memSel, List<ActualBinding> args)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(cce.NonNullElements(lhs));
    Contract.Requires(memSel != null);
    Contract.Requires(memSel.Member is Method);
    Contract.Requires(cce.NonNullElements(args));

    this.Lhs = lhs;
    this.MethodSelect = memSel;
    this.Bindings = new ActualBindings(args);
  }

  /// <summary>
  /// This constructor is intended to be used when constructing a resolved CallStmt. The "args" are expected
  /// to be already resolved, and are all given positionally.
  /// </summary>
  public CallStmt(IToken tok, IToken endTok, List<Expression> lhs, MemberSelectExpr memSel, List<Expression> args)
    : this(tok, endTok, lhs, memSel, args.ConvertAll(e => new ActualBinding(null, e))) {
    Bindings.AcceptArgumentExpressionsAsExactParameterList();
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      foreach (var ee in Lhs) {
        yield return ee;
      }
      yield return MethodSelect;
      foreach (var ee in Args) {
        yield return ee;
      }
    }
  }
}

public class BlockStmt : Statement, IRegion {
  public readonly List<Statement> Body;

  IToken IRegion.BodyStartTok => Tok;
  IToken IRegion.BodyEndTok => EndTok;

  public BlockStmt(IToken tok, IToken endTok, [Captured] List<Statement> body)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(cce.NonNullElements(body));
    this.Body = body;
  }

  public override IEnumerable<Statement> SubStatements {
    get { return Body; }
  }

  public virtual void AppendStmt(Statement s) {
    Contract.Requires(s != null);
    Body.Add(s);
  }
}

/**
   * Used by two phase constructors: https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#13323-two-phase-constructors
   */
public class DividedBlockStmt : BlockStmt {
  public readonly List<Statement> BodyInit;  // first part of Body's statements
  public readonly IToken SeparatorTok;  // token that separates the two parts, if any
  public readonly List<Statement> BodyProper;  // second part of Body's statements
  public DividedBlockStmt(IToken tok, IToken endTok, List<Statement> bodyInit, IToken/*?*/ separatorTok, List<Statement> bodyProper)
    : base(tok, endTok, Util.Concat(bodyInit, bodyProper)) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(cce.NonNullElements(bodyInit));
    Contract.Requires(cce.NonNullElements(bodyProper));
    this.BodyInit = bodyInit;
    this.SeparatorTok = separatorTok;
    this.BodyProper = bodyProper;
  }
  public override void AppendStmt(Statement s) {
    BodyProper.Add(s);
    base.AppendStmt(s);
  }
}

public class IfStmt : Statement {
  public readonly bool IsBindingGuard;
  public readonly Expression Guard;
  public readonly BlockStmt Thn;
  public readonly Statement Els;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(!IsBindingGuard || (Guard is ExistsExpr && ((ExistsExpr)Guard).Range == null));
    Contract.Invariant(Thn != null);
    Contract.Invariant(Els == null || Els is BlockStmt || Els is IfStmt || Els is SkeletonStatement);
  }
  public IfStmt(IToken tok, IToken endTok, bool isBindingGuard, Expression guard, BlockStmt thn, Statement els)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
    Contract.Requires(thn != null);
    Contract.Requires(els == null || els is BlockStmt || els is IfStmt || els is SkeletonStatement);
    this.IsBindingGuard = isBindingGuard;
    this.Guard = guard;
    this.Thn = thn;
    this.Els = els;
  }
  public IfStmt(IToken tok, IToken endTok, bool isBindingGuard, Expression guard, BlockStmt thn, Statement els, Attributes attrs)
    : base(tok, endTok, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
    Contract.Requires(thn != null);
    Contract.Requires(els == null || els is BlockStmt || els is IfStmt || els is SkeletonStatement);
    this.IsBindingGuard = isBindingGuard;
    this.Guard = guard;
    this.Thn = thn;
    this.Els = els;
  }
  public override IEnumerable<Statement> SubStatements {
    get {
      yield return Thn;
      if (Els != null) {
        yield return Els;
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

public class GuardedAlternative : IAttributeBearingDeclaration {
  public readonly IToken Tok;
  public readonly bool IsBindingGuard;
  public readonly Expression Guard;
  public readonly List<Statement> Body;
  public Attributes Attributes;
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

public class AlternativeStmt : Statement {
  public readonly bool UsesOptionalBraces;
  public readonly List<GuardedAlternative> Alternatives;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Alternatives != null);
  }
  public AlternativeStmt(IToken tok, IToken endTok, List<GuardedAlternative> alternatives, bool usesOptionalBraces)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(alternatives != null);
    this.Alternatives = alternatives;
    this.UsesOptionalBraces = usesOptionalBraces;
  }
  public AlternativeStmt(IToken tok, IToken endTok, List<GuardedAlternative> alternatives, bool usesOptionalBraces, Attributes attrs)
    : base(tok, endTok, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(alternatives != null);
    this.Alternatives = alternatives;
    this.UsesOptionalBraces = usesOptionalBraces;
  }
  public override IEnumerable<Statement> SubStatements {
    get {
      foreach (var alt in Alternatives) {
        foreach (var s in alt.Body) {
          yield return s;
        }
      }
    }
  }
  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      foreach (var alt in Alternatives) {
        yield return alt.Guard;
      }
    }
  }
}

public abstract class LoopStmt : Statement, IDeclarationOrUsage {
  public readonly List<AttributedExpression> Invariants;
  public readonly Specification<Expression> Decreases;
  [FilledInDuringResolution] public bool InferredDecreases;  // says that no explicit "decreases" clause was given and an attempt was made to find one automatically (which may or may not have produced anything)
  public readonly Specification<FrameExpression> Mod;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Invariants));
    Contract.Invariant(Decreases != null);
    Contract.Invariant(Mod != null);
  }
  public LoopStmt(IToken tok, IToken endTok, List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(cce.NonNullElements(invariants));
    Contract.Requires(decreases != null);
    Contract.Requires(mod != null);

    this.Invariants = invariants;
    this.Decreases = decreases;
    this.Mod = mod;
  }
  public LoopStmt(IToken tok, IToken endTok, List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod, Attributes attrs)
    : base(tok, endTok, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(cce.NonNullElements(invariants));
    Contract.Requires(decreases != null);
    Contract.Requires(mod != null);

    this.Invariants = invariants;
    this.Decreases = decreases;
    this.Mod = mod;
  }
  public IEnumerable<Expression> LoopSpecificationExpressions {
    get {
      foreach (var mfe in Invariants) {
        foreach (var e in Attributes.SubExpressions(mfe.Attributes)) { yield return e; }
        yield return mfe.E;
      }
      foreach (var e in Attributes.SubExpressions(Decreases.Attributes)) { yield return e; }
      if (Decreases.Expressions != null) {
        foreach (var e in Decreases.Expressions) {
          yield return e;
        }
      }
      foreach (var e in Attributes.SubExpressions(Mod.Attributes)) { yield return e; }
      if (Mod.Expressions != null) {
        foreach (var fe in Mod.Expressions) {
          yield return fe.E;
        }
      }
    }
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) {
        yield return e;
      }
    }
  }

  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in LoopSpecificationExpressions) {
        yield return e;
      }
    }
  }

  public IToken NameToken => Tok;
}

public abstract class OneBodyLoopStmt : LoopStmt {
  public readonly BlockStmt/*?*/ Body;
  public WhileStmt.LoopBodySurrogate/*?*/ BodySurrogate;  // set by Resolver; remains null unless Body==null

  public OneBodyLoopStmt(IToken tok, IToken endTok,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    BlockStmt /*?*/ body, Attributes/*?*/ attrs)
    : base(tok, endTok, invariants, decreases, mod, attrs) {
    Body = body;
  }

  public override IEnumerable<Statement> SubStatements {
    get {
      if (Body != null) {
        yield return Body;
      }
    }
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

public class ForLoopStmt : OneBodyLoopStmt {
  public readonly BoundVar LoopIndex;
  public readonly Expression Start;
  public readonly Expression/*?*/ End;
  public readonly bool GoingUp;

  public ForLoopStmt(IToken tok, IToken endTok, BoundVar loopIndexVariable, Expression start, Expression/*?*/ end, bool goingUp,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    BlockStmt /*?*/ body, Attributes attrs)
    : base(tok, endTok, invariants, decreases, mod, body, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(loopIndexVariable != null);
    Contract.Requires(start != null);
    Contract.Requires(invariants != null);
    Contract.Requires(decreases != null);
    Contract.Requires(mod != null);
    LoopIndex = loopIndexVariable;
    Start = start;
    End = end;
    GoingUp = goingUp;
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      yield return Start;
      if (End != null) {
        yield return End;
      }
    }
  }
}

public class AlternativeLoopStmt : LoopStmt {
  public readonly bool UsesOptionalBraces;
  public readonly List<GuardedAlternative> Alternatives;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Alternatives != null);
  }
  public AlternativeLoopStmt(IToken tok, IToken endTok,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    List<GuardedAlternative> alternatives, bool usesOptionalBraces)
    : base(tok, endTok, invariants, decreases, mod) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(alternatives != null);
    this.Alternatives = alternatives;
    this.UsesOptionalBraces = usesOptionalBraces;
  }
  public AlternativeLoopStmt(IToken tok, IToken endTok,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    List<GuardedAlternative> alternatives, bool usesOptionalBraces, Attributes attrs)
    : base(tok, endTok, invariants, decreases, mod, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(alternatives != null);
    this.Alternatives = alternatives;
    this.UsesOptionalBraces = usesOptionalBraces;
  }
  public override IEnumerable<Statement> SubStatements {
    get {
      foreach (var alt in Alternatives) {
        foreach (var s in alt.Body) {
          yield return s;
        }
      }
    }
  }
  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      foreach (var alt in Alternatives) {
        yield return alt.Guard;
      }
    }
  }
}

public class ForallStmt : Statement {
  public readonly List<BoundVar> BoundVars;  // note, can be the empty list, in which case Range denotes "true"
  public Expression Range;  // mostly readonly, except that it may in some cases be updated during resolution to conjoin the precondition of the call in the body
  public readonly List<AttributedExpression> Ens;
  public readonly Statement Body;
  public List<Expression> ForallExpressions;   // fill in by rewriter.
  public bool CanConvert = true; //  can convert to ForallExpressions

  [FilledInDuringResolution] public List<ComprehensionExpr.BoundedPool> Bounds;
  // invariant: if successfully resolved, Bounds.Count == BoundVars.Count;

  /// <summary>
  /// Assign means there are no ensures clauses and the body consists of one update statement,
  ///   either to an object field or to an array.
  /// Call means there are no ensures clauses and the body consists of a single call to a (presumably
  ///   ghost, but non-ghost is also allowed) method with no out-parameters and an empty modifies
  ///   clause.
  /// Proof means there is at least one ensures clause, and the body consists of any (presumably ghost,
  ///   but non-ghost is also allowed) code without side effects on variables (including fields and array
  ///   elements) declared outside the body itself.
  /// Notes:
  /// * More kinds may be allowed in the future.
  /// * One could also allow Call to call non-ghost methods without side effects.  However, that
  ///   would seem pointless in the program, so they are disallowed (to avoid any confusion that
  ///   such use of the forall statement might actually have a point).
  /// * One could allow Proof even without ensures clauses that "export" what was learned.
  ///   However, that might give the false impression that the body is nevertheless exported.
  /// </summary>
  public enum BodyKind { Assign, Call, Proof }
  [FilledInDuringResolution] public BodyKind Kind;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(BoundVars != null);
    Contract.Invariant(Range != null);
    Contract.Invariant(BoundVars.Count != 0 || LiteralExpr.IsTrue(Range));
    Contract.Invariant(Ens != null);
  }

  public ForallStmt(IToken tok, IToken endTok, List<BoundVar> boundVars, Attributes attrs, Expression range, List<AttributedExpression> ens, Statement body)
    : base(tok, endTok, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(cce.NonNullElements(boundVars));
    Contract.Requires(range != null);
    Contract.Requires(boundVars.Count != 0 || LiteralExpr.IsTrue(range));
    Contract.Requires(cce.NonNullElements(ens));
    this.BoundVars = boundVars;
    this.Range = range;
    this.Ens = ens;
    this.Body = body;
  }

  public Statement S0 {
    get {
      // dig into Body to find a single statement
      Statement s = this.Body;
      while (true) {
        var block = s as BlockStmt;
        if (block != null && block.Body.Count == 1) {
          s = block.Body[0];
          // dig further into s
        } else if (s is UpdateStmt) {
          var update = (UpdateStmt)s;
          if (update.ResolvedStatements.Count == 1) {
            s = update.ResolvedStatements[0];
            // dig further into s
          } else {
            return s;
          }
        } else {
          return s;
        }
      }
    }
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
      foreach (var e in base.NonSpecificationSubExpressions) {
        yield return e;
      }

      yield return Range;
    }
  }
  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) {
        yield return e;
      }
      foreach (var ee in Ens) {
        foreach (var e in Attributes.SubExpressions(ee.Attributes)) { yield return e; }
        yield return ee.E;
      }
    }
  }

  public List<BoundVar> UncompilableBoundVars() {
    Contract.Ensures(Contract.Result<List<BoundVar>>() != null);
    var v = ComprehensionExpr.BoundedPool.PoolVirtues.Finite | ComprehensionExpr.BoundedPool.PoolVirtues.Enumerable;
    return ComprehensionExpr.BoundedPool.MissingBounds(BoundVars, Bounds, v);
  }
}

public class ModifyStmt : Statement {
  public readonly Specification<FrameExpression> Mod;
  public readonly BlockStmt Body;

  public ModifyStmt(IToken tok, IToken endTok, List<FrameExpression> mod, Attributes attrs, BlockStmt body)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(mod != null);
    Mod = new Specification<FrameExpression>(mod, attrs);
    Body = body;
  }

  public override IEnumerable<Statement> SubStatements {
    get {
      if (Body != null) {
        yield return Body;
      }
    }
  }
  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      foreach (var e in Attributes.SubExpressions(Mod.Attributes)) { yield return e; }
      foreach (var fe in Mod.Expressions) {
        yield return fe.E;
      }
    }
  }
}

public class CalcStmt : Statement {
  public abstract class CalcOp {
    /// <summary>
    /// Resulting operator "x op z" if "x this y" and "y other z".
    /// Returns null if this and other are incompatible.
    /// </summary>
    [Pure]
    public abstract CalcOp ResultOp(CalcOp other);

    /// <summary>
    /// Returns an expression "line0 this line1".
    /// </summary>
    [Pure]
    public abstract Expression StepExpr(Expression line0, Expression line1);
  }

  public class BinaryCalcOp : CalcOp {
    public readonly BinaryExpr.Opcode Op;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(ValidOp(Op));
    }

    /// <summary>
    /// Is op a valid calculation operator?
    /// </summary>
    [Pure]
    public static bool ValidOp(BinaryExpr.Opcode op) {
      return
        op == BinaryExpr.Opcode.Eq || op == BinaryExpr.Opcode.Neq
                                   || op == BinaryExpr.Opcode.Lt || op == BinaryExpr.Opcode.Le
                                   || op == BinaryExpr.Opcode.Gt || op == BinaryExpr.Opcode.Ge
                                   || LogicOp(op);
    }

    /// <summary>
    /// Is op a valid operator only for Boolean lines?
    /// </summary>
    [Pure]
    public static bool LogicOp(BinaryExpr.Opcode op) {
      return op == BinaryExpr.Opcode.Iff || op == BinaryExpr.Opcode.Imp || op == BinaryExpr.Opcode.Exp;
    }

    public BinaryCalcOp(BinaryExpr.Opcode op) {
      Contract.Requires(ValidOp(op));
      Op = op;
    }

    /// <summary>
    /// Does this subsume other (this . other == other . this == this)?
    /// </summary>
    private bool Subsumes(BinaryCalcOp other) {
      Contract.Requires(other != null);
      var op1 = Op;
      var op2 = other.Op;
      if (op1 == BinaryExpr.Opcode.Neq || op2 == BinaryExpr.Opcode.Neq) {
        return op2 == BinaryExpr.Opcode.Eq;
      }

      if (op1 == op2) {
        return true;
      }

      if (LogicOp(op1) || LogicOp(op2)) {
        return op2 == BinaryExpr.Opcode.Eq ||
               (op1 == BinaryExpr.Opcode.Imp && op2 == BinaryExpr.Opcode.Iff) ||
               (op1 == BinaryExpr.Opcode.Exp && op2 == BinaryExpr.Opcode.Iff) ||
               (op1 == BinaryExpr.Opcode.Eq && op2 == BinaryExpr.Opcode.Iff);
      }

      return op2 == BinaryExpr.Opcode.Eq ||
             (op1 == BinaryExpr.Opcode.Lt && op2 == BinaryExpr.Opcode.Le) ||
             (op1 == BinaryExpr.Opcode.Gt && op2 == BinaryExpr.Opcode.Ge);
    }

    public override CalcOp ResultOp(CalcOp other) {
      if (other is BinaryCalcOp) {
        var o = (BinaryCalcOp)other;
        if (this.Subsumes(o)) {
          return this;
        } else if (o.Subsumes(this)) {
          return other;
        }
        return null;
      } else if (other is TernaryCalcOp) {
        return other.ResultOp(this);
      } else {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }
    }

    public override Expression StepExpr(Expression line0, Expression line1) {
      if (Op == BinaryExpr.Opcode.Exp) {
        // The order of operands is reversed so that it can be turned into implication during resolution
        return new BinaryExpr(line0.tok, Op, line1, line0);
      } else {
        return new BinaryExpr(line0.tok, Op, line0, line1);
      }
    }

    public override string ToString() {
      return BinaryExpr.OpcodeString(Op);
    }

  }

  public class TernaryCalcOp : CalcOp {
    public readonly Expression Index; // the only allowed ternary operator is ==#, so we only store the index

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Index != null);
    }

    public TernaryCalcOp(Expression idx) {
      Contract.Requires(idx != null);
      Index = idx;
    }

    public override CalcOp ResultOp(CalcOp other) {
      if (other is BinaryCalcOp) {
        if (((BinaryCalcOp)other).Op == BinaryExpr.Opcode.Eq) {
          return this;
        }
        return null;
      } else if (other is TernaryCalcOp) {
        var a = Index;
        var b = ((TernaryCalcOp)other).Index;
        var minIndex = new ITEExpr(a.tok, false, new BinaryExpr(a.tok, BinaryExpr.Opcode.Le, a, b), a, b);
        return new TernaryCalcOp(minIndex); // ToDo: if we could compare expressions for syntactic equalty, we could use this here to optimize
      } else {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }
    }

    public override Expression StepExpr(Expression line0, Expression line1) {
      return new TernaryExpr(line0.tok, TernaryExpr.Opcode.PrefixEqOp, Index, line0, line1);
    }

    public override string ToString() {
      return "==#";
    }

  }

  public readonly List<Expression> Lines;    // Last line is dummy, in order to form a proper step with the dangling hint
  public readonly List<BlockStmt> Hints;     // Hints[i] comes after line i; block statement is used as a container for multiple sub-hints
  public readonly CalcOp UserSuppliedOp;     // may be null, if omitted by the user
  public CalcOp Op;                          // main operator of the calculation (either UserSuppliedOp or (after resolution) an inferred CalcOp)
  public readonly List<CalcOp/*?*/> StepOps; // StepOps[i] comes after line i
  [FilledInDuringResolution] public readonly List<Expression> Steps;    // expressions li op l<i + 1> (last step is dummy)
  [FilledInDuringResolution] public Expression Result;                  // expression l0 ResultOp ln

  public static readonly CalcOp DefaultOp = new BinaryCalcOp(BinaryExpr.Opcode.Eq);

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Lines != null);
    Contract.Invariant(cce.NonNullElements(Lines));
    Contract.Invariant(Hints != null);
    Contract.Invariant(cce.NonNullElements(Hints));
    Contract.Invariant(StepOps != null);
    Contract.Invariant(Steps != null);
    Contract.Invariant(cce.NonNullElements(Steps));
    Contract.Invariant(Hints.Count == Math.Max(Lines.Count - 1, 0));
    Contract.Invariant(StepOps.Count == Hints.Count);
  }

  public CalcStmt(IToken tok, IToken endTok, CalcOp userSuppliedOp, List<Expression> lines, List<BlockStmt> hints, List<CalcOp/*?*/> stepOps, Attributes attrs)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(lines != null);
    Contract.Requires(hints != null);
    Contract.Requires(stepOps != null);
    Contract.Requires(cce.NonNullElements(lines));
    Contract.Requires(cce.NonNullElements(hints));
    Contract.Requires(hints.Count == Math.Max(lines.Count - 1, 0));
    Contract.Requires(stepOps.Count == hints.Count);
    this.UserSuppliedOp = userSuppliedOp;
    this.Lines = lines;
    this.Hints = hints;
    this.StepOps = stepOps;
    this.Steps = new List<Expression>();
    this.Result = null;
    this.Attributes = attrs;
  }

  public override IEnumerable<Statement> SubStatements {
    get {
      foreach (var h in Hints) {
        yield return h;
      }
    }
  }
  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      foreach (var e in Attributes.SubExpressions(Attributes)) { yield return e; }

      for (int i = 0; i < Lines.Count - 1; i++) {  // note, we skip the duplicated line at the end
        yield return Lines[i];
      }
      foreach (var calcop in AllCalcOps) {
        var o3 = calcop as TernaryCalcOp;
        if (o3 != null) {
          yield return o3.Index;
        }
      }
    }
  }

  IEnumerable<CalcOp> AllCalcOps {
    get {
      if (UserSuppliedOp != null) {
        yield return UserSuppliedOp;
      }
      foreach (var stepop in StepOps) {
        if (stepop != null) {
          yield return stepop;
        }
      }
    }
  }

  /// <summary>
  /// Left-hand side of a step expression.
  /// Note that Lhs(op.StepExpr(line0, line1)) != line0 when op is <==.
  /// </summary>
  public static Expression Lhs(Expression step) {
    Contract.Requires(step is BinaryExpr || step is TernaryExpr);
    if (step is BinaryExpr) {
      return ((BinaryExpr)step).E0;
    } else {
      return ((TernaryExpr)step).E1;
    }
  }

  /// <summary>
  /// Right-hand side of a step expression.
  /// Note that Rhs(op.StepExpr(line0, line1)) != line1 when op is REVERSE-IMPLICATION.
  /// </summary>
  public static Expression Rhs(Expression step) {
    Contract.Requires(step is BinaryExpr || step is TernaryExpr);
    if (step is BinaryExpr) {
      return ((BinaryExpr)step).E1;
    } else {
      return ((TernaryExpr)step).E2;
    }
  }
}

public class MatchStmt : Statement {
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Source != null);
    Contract.Invariant(cce.NonNullElements(Cases));
    Contract.Invariant(cce.NonNullElements(MissingCases));
  }

  private Expression source;
  private List<MatchCaseStmt> cases;
  public readonly MatchingContext Context;
  [FilledInDuringResolution] public readonly List<DatatypeCtor> MissingCases = new List<DatatypeCtor>();
  public readonly bool UsesOptionalBraces;
  public MatchStmt OrigUnresolved;  // the resolver makes this clone of the MatchStmt before it starts desugaring it
  public MatchStmt(IToken tok, IToken endTok, Expression source, [Captured] List<MatchCaseStmt> cases, bool usesOptionalBraces, MatchingContext context = null)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(source != null);
    Contract.Requires(cce.NonNullElements(cases));
    this.source = source;
    this.cases = cases;
    this.UsesOptionalBraces = usesOptionalBraces;
    this.Context = context is null ? new HoleCtx() : context;
  }
  public MatchStmt(IToken tok, IToken endTok, Expression source, [Captured] List<MatchCaseStmt> cases, bool usesOptionalBraces, Attributes attrs, MatchingContext context = null)
    : base(tok, endTok, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(source != null);
    Contract.Requires(cce.NonNullElements(cases));
    this.source = source;
    this.cases = cases;
    this.UsesOptionalBraces = usesOptionalBraces;
    this.Context = context is null ? new HoleCtx() : context;
  }

  public Expression Source {
    get { return source; }
  }

  public List<MatchCaseStmt> Cases {
    get { return cases; }
  }

  // should only be used in desugar in resolve to change the cases of the matchexpr
  public void UpdateSource(Expression source) {
    this.source = source;
  }

  public void UpdateCases(List<MatchCaseStmt> cases) {
    this.cases = cases;
  }

  public override IEnumerable<Statement> SubStatements {
    get {
      foreach (var kase in cases) {
        foreach (var s in kase.Body) {
          yield return s;
        }
      }
    }
  }
  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      yield return Source;
    }
  }
}

public class MatchCaseStmt : MatchCase {
  private List<Statement> body;
  public Attributes Attributes;
  // Has the case for this constructor been generated by the resolver because the pattern was
  // a bound variable, or was it an explicit constructor case in the source code? E.g.,
  //
  // var x: Option<bool>;
  // match x
  //   case Some(true) => ... // FromBoundVar == false
  //   case Some(_)    => ... // FromBoundVar == false
  //   case v          => ... // FromBoundVar == true
  //   case _ =>       => ... // FromBoundVar == true (this case would be unreachable; added for illustration purposes)
  //
  // The resolved Dafny AST desugars pattern matching in a way that makes it challenging to restore the shape of the
  // original pattern match; in particular, matching against a bound variable (or underscore) is resolved into a
  // set of matches against all unmatched constructors. The `FromBoundVar` field provides information to code that
  // operates on the resolved AST and that is interested in the shape of the parsed AST.
  // This field is currently not used in the compiler but is useful for extensions and third-party compilers that
  // use this compiler as a frontend.
  public readonly bool FromBoundVar;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Body));
  }

  public override IEnumerable<INode> Children => body;

  public MatchCaseStmt(IToken tok, DatatypeCtor ctor, bool FromBoundVar, [Captured] List<BoundVar> arguments, [Captured] List<Statement> body, Attributes attrs = null)
    : base(tok, ctor, arguments) {
    Contract.Requires(tok != null);
    Contract.Requires(ctor != null);
    Contract.Requires(cce.NonNullElements(arguments));
    Contract.Requires(cce.NonNullElements(body));
    this.body = body;
    this.Attributes = attrs;
    this.FromBoundVar = FromBoundVar;
  }

  public List<Statement> Body {
    get { return body; }
  }

  // should only be called by resolve to reset the body of the MatchCaseExpr
  public void UpdateBody(List<Statement> body) {
    this.body = body;
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
