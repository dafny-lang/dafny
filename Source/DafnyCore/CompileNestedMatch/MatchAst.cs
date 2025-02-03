using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class MatchExpr : Expression, IMatch, ICloneable<MatchExpr> {  // a MatchExpr is an "extended expression" and is only allowed in certain places
  private Expression source;
  private List<MatchCaseExpr> cases;
  public readonly MatchingContext Context;
  [FilledInDuringResolution] public List<DatatypeCtor> MissingCases { get; } = [];
  public readonly bool UsesOptionalBraces;
  public MatchExpr OrigUnresolved;  // the resolver makes this clone of the MatchExpr before it starts desugaring it

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Source != null);
    Contract.Invariant(cce.NonNullElements(Cases));
    Contract.Invariant(cce.NonNullElements(MissingCases));
  }

  public MatchExpr(IOrigin origin, Expression source, [Captured] List<MatchCaseExpr> cases, bool usesOptionalBraces, MatchingContext context = null)
    : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(source != null);
    Contract.Requires(cce.NonNullElements(cases));
    this.source = source;
    this.cases = cases;
    UsesOptionalBraces = usesOptionalBraces;
    Context = context ?? new HoleCtx();
  }
  public MatchExpr(Cloner cloner, MatchExpr original)
    : base(cloner, original) {
    source = cloner.CloneExpr(original.Source);
    cases = original.Cases.ConvertAll(cloner.CloneMatchCaseExpr);
    UsesOptionalBraces = original.UsesOptionalBraces;
    Context = original.Context;
    if (cloner.CloneResolvedFields) {
      MissingCases = original.MissingCases;
    }
  }

  public MatchExpr Clone(Cloner cloner) {
    return new MatchExpr(cloner, this);
  }

  public Expression Source => source;

  public List<MatchCaseExpr> Cases => cases;

  IEnumerable<MatchCase> IMatch.Cases => Cases;

  // should only be used in desugar in resolve to change the source and cases of the matchexpr
  public void UpdateSource(Expression source) {
    this.source = source;
  }

  public void UpdateCases(List<MatchCaseExpr> cases) {
    this.cases = cases;
  }

  public override IEnumerable<INode> Children => new[] { source }.Concat<Node>(cases);

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return Source;
      foreach (var mc in cases) {
        yield return mc.Body;
      }
    }
  }

  public override IEnumerable<Type> ComponentTypes {
    get {
      foreach (var mc in cases) {
        foreach (var bv in mc.Arguments) {
          yield return bv.Type;
        }
      }
    }
  }
}

public abstract class MatchCase : NodeWithComputedRange, IHasReferences {
  public DatatypeCtor Ctor;
  public List<BoundVar> Arguments;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Origin != null);
    Contract.Invariant(Ctor != null);
    Contract.Invariant(cce.NonNullElements(Arguments));
  }

  public MatchCase(IOrigin origin, DatatypeCtor ctor, [Captured] List<BoundVar> arguments) : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(ctor != null);
    Contract.Requires(cce.NonNullElements(arguments));
    Ctor = ctor;
    Arguments = arguments;
  }

  public IEnumerable<Reference> GetReferences() {
    return new[] { new Reference(Origin, Ctor) };
  }
}

public interface IMatch {
  IEnumerable<MatchCase> Cases { get; }
  Expression Source { get; }
  List<DatatypeCtor> MissingCases { get; }
}

public class MatchStmt : Statement, IMatch, ICloneable<MatchStmt> {
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Source != null);
    Contract.Invariant(cce.NonNullElements(Cases));
    Contract.Invariant(cce.NonNullElements(MissingCases));
  }

  private Expression source;
  private List<MatchCaseStmt> cases;
  public readonly MatchingContext Context;
  [FilledInDuringResolution] public List<DatatypeCtor> MissingCases { get; } = [];
  public readonly bool UsesOptionalBraces;

  public MatchStmt Clone(Cloner cloner) {
    return new MatchStmt(cloner, this);
  }

  public MatchStmt(Cloner cloner, MatchStmt original) : base(cloner, original) {
    source = cloner.CloneExpr(original.Source);
    cases = original.cases.Select(cloner.CloneMatchCaseStmt).ToList();
    Context = original.Context;
    UsesOptionalBraces = original.UsesOptionalBraces;

    if (cloner.CloneResolvedFields) {
      MissingCases = original.MissingCases;
    }
  }

  public MatchStmt(IOrigin origin, Expression source, [Captured] List<MatchCaseStmt> cases,
    bool usesOptionalBraces, MatchingContext context = null)
    : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(source != null);
    Contract.Requires(cce.NonNullElements(cases));
    this.source = source;
    this.cases = cases;
    UsesOptionalBraces = usesOptionalBraces;
    Context = context is null ? new HoleCtx() : context;
  }

  public MatchStmt(IOrigin origin, Expression source, [Captured] List<MatchCaseStmt> cases,
    bool usesOptionalBraces, Attributes attrs, MatchingContext context = null)
    : base(origin, attrs) {
    Contract.Requires(origin != null);
    Contract.Requires(source != null);
    Contract.Requires(cce.NonNullElements(cases));
    this.source = source;
    this.cases = cases;
    UsesOptionalBraces = usesOptionalBraces;
    Context = context is null ? new HoleCtx() : context;
  }

  public Expression Source => source;

  public List<MatchCaseStmt> Cases => cases;
  IEnumerable<MatchCase> IMatch.Cases => Cases;

  public override IEnumerable<INode> Children => new[] { Source }.Concat<Node>(Cases);

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext, string proofContext,
    bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    IsGhost = mustBeErasable || ExpressionTester.UsesSpecFeatures(Source) || ExpressionTester.FirstCaseThatDependsOnGhostCtor(Cases) != null;
    if (!mustBeErasable && IsGhost) {
      reporter.Info(MessageSource.Resolver, Origin, "ghost match");
    }

    Cases.ForEach(kase => kase.Body.ForEach(ss => ss.ResolveGhostness(resolver, reporter, IsGhost, codeContext,
      proofContext, allowAssumptionVariables, inConstructorInitializationPhase)));
    IsGhost = IsGhost || Cases.All(kase => kase.Body.All(ss => ss.IsGhost));
    if (!IsGhost) {
      // If there were features in the source expression that are treated differently in ghost and non-ghost
      // contexts, make sure they get treated for non-ghost use.
      ExpressionTester.CheckIsCompilable(resolver, reporter, Source, codeContext);
    }
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
      foreach (var e in base.NonSpecificationSubExpressions) {
        yield return e;
      }

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
  public override IEnumerable<INode> PreResolveChildren => Children;

  public MatchCaseStmt(IOrigin rangeOrigin, DatatypeCtor ctor, bool fromBoundVar, [Captured] List<BoundVar> arguments, [Captured] List<Statement> body, Attributes attrs = null)
    : base(rangeOrigin, ctor, arguments) {
    Contract.Requires(ctor != null);
    Contract.Requires(cce.NonNullElements(arguments));
    Contract.Requires(cce.NonNullElements(body));
    this.body = body;
    Attributes = attrs;
    FromBoundVar = fromBoundVar;
  }

  public List<Statement> Body {
    get { return body; }
  }

  // should only be called by resolve to reset the body of the MatchCaseExpr
  public void UpdateBody(List<Statement> body) {
    this.body = body;
  }
}

public class MatchCaseExpr : MatchCase {
  private Expression body;
  public Attributes Attributes;
  public readonly bool FromBoundVar;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(body != null);
  }

  public override IEnumerable<INode> Children => Arguments.Concat<Node>(new[] { body });
  public override IEnumerable<INode> PreResolveChildren => Children;

  public MatchCaseExpr(IOrigin origin, DatatypeCtor ctor, bool FromBoundVar, [Captured] List<BoundVar> arguments, Expression body, Attributes attrs = null)
    : base(origin, ctor, arguments) {
    Contract.Requires(origin != null);
    Contract.Requires(ctor != null);
    Contract.Requires(cce.NonNullElements(arguments));
    Contract.Requires(body != null);
    this.body = body;
    Attributes = attrs;
    this.FromBoundVar = FromBoundVar;
  }

  public Expression Body {
    get { return body; }
  }

  // should only be called by resolve to reset the body of the MatchCaseExpr
  public void UpdateBody(Expression body) {
    this.body = body;
  }
}

/*
MatchingContext represents the context
in which a pattern-match takes place during pattern-matching compilation

MatchingContext is either:
1 - a HoleCtx
    standing for one of the current selectors in pattern-matching compilation
2 - A ForallCtx
    standing for a pattern-match over any expression
3 - an IdCtx of a string and a list of MatchingContext
    standing for a pattern-match over a constructor
4 - a LitCtx
    standing for a pattern-match over a constant
*/
public abstract class MatchingContext {
  public virtual MatchingContext AbstractAllHoles() {
    return this;
  }

  public MatchingContext AbstractHole() {
    return FillHole(new ForallCtx());
  }

  public virtual MatchingContext FillHole(MatchingContext curr) {
    return this;
  }
}

public class LitCtx : MatchingContext {
  public readonly LiteralExpr Lit;

  public LitCtx(LiteralExpr lit) {
    Contract.Requires(lit != null);
    Lit = lit;
  }

  public override string ToString() {
    return Printer.ExprToString(DafnyOptions.DefaultImmutableOptions, Lit);
  }
}

public class HoleCtx : MatchingContext {
  public HoleCtx() { }

  public override string ToString() {
    return "*";
  }

  public override MatchingContext AbstractAllHoles() {
    return new ForallCtx();
  }

  public override MatchingContext FillHole(MatchingContext curr) {
    return curr;
  }
}

public class ForallCtx : MatchingContext {
  public ForallCtx() { }

  public override string ToString() {
    return "_";
  }
}

public class IdCtx : MatchingContext {
  public readonly string Id;
  public readonly List<MatchingContext> Arguments;

  public IdCtx(string id, List<MatchingContext> arguments) {
    Contract.Requires(id != null);
    Contract.Requires(arguments != null); // Arguments can be empty, but shouldn't be null
    Id = id;
    Arguments = arguments;
  }

  public IdCtx(DatatypeCtor ctor) {
    List<MatchingContext> arguments = Enumerable.Repeat((MatchingContext)new HoleCtx(), ctor.Formals.Count).ToList();
    Id = ctor.Name;
    Arguments = arguments;
  }

  public override string ToString() {
    if (Arguments.Count == 0) {
      return Id;
    } else {
      List<string> cps = Arguments.ConvertAll<string>(x => x.ToString());
      return string.Format("{0}({1})", Id, string.Join(", ", cps));
    }
  }

  public override MatchingContext AbstractAllHoles() {
    return new IdCtx(Id, Arguments.ConvertAll<MatchingContext>(x => x.AbstractAllHoles()));
  }

  // Find the first (leftmost) occurrence of HoleCtx and replace it with curr
  // Returns false if no HoleCtx is found
  private bool ReplaceLeftmost(MatchingContext curr, out MatchingContext newContext) {
    var newArguments = new List<MatchingContext>();
    bool foundHole = false;
    int currArgIndex = 0;

    while (!foundHole && currArgIndex < Arguments.Count) {
      var arg = Arguments.ElementAt(currArgIndex);
      switch (arg) {
        case HoleCtx _:
          foundHole = true;
          newArguments.Add(curr);
          break;
        case IdCtx argId:
          foundHole = argId.ReplaceLeftmost(curr, out var newarg);
          newArguments.Add(newarg);
          break;
        default:
          newArguments.Add(arg);
          break;
      }
      currArgIndex++;
    }

    if (foundHole) {
      while (currArgIndex < Arguments.Count) {
        newArguments.Add(Arguments.ElementAt(currArgIndex));
        currArgIndex++;
      }
    }

    newContext = new IdCtx(Id, newArguments);
    return foundHole;
  }

  public override MatchingContext FillHole(MatchingContext curr) {
    ReplaceLeftmost(curr, out var newContext);
    return newContext;
  }
}
