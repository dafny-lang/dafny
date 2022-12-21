using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny; 

public class MatchExpr : Expression {  // a MatchExpr is an "extended expression" and is only allowed in certain places
  private Expression source;
  private List<MatchCaseExpr> cases;
  public readonly MatchingContext Context;
  [FilledInDuringResolution] public readonly List<DatatypeCtor> MissingCases = new();
  public readonly bool UsesOptionalBraces;
  public MatchExpr OrigUnresolved;  // the resolver makes this clone of the MatchExpr before it starts desugaring it

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Source != null);
    Contract.Invariant(cce.NonNullElements(Cases));
    Contract.Invariant(cce.NonNullElements(MissingCases));
  }

  public MatchExpr(IToken tok, Expression source, [Captured] List<MatchCaseExpr> cases, bool usesOptionalBraces, MatchingContext context = null)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(source != null);
    Contract.Requires(cce.NonNullElements(cases));
    this.source = source;
    this.cases = cases;
    this.UsesOptionalBraces = usesOptionalBraces;
    this.Context = context is null ? new HoleCtx() : context;
  }

  public Expression Source => source;

  public List<MatchCaseExpr> Cases => cases;

  // should only be used in desugar in resolve to change the source and cases of the matchexpr
  public void UpdateSource(Expression source) {
    this.source = source;
  }

  public void UpdateCases(List<MatchCaseExpr> cases) {
    this.cases = cases;
  }

  public override IEnumerable<INode> Children => new[] { source }.Concat<INode>(cases);

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

public abstract class MatchCase : INode, IHasUsages {
  [FilledInDuringResolution] public DatatypeCtor Ctor;
  public List<BoundVar> Arguments; // created by the resolver.

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(tok != null);
    Contract.Invariant(Ctor != null);
    Contract.Invariant(cce.NonNullElements(Arguments));
  }

  public MatchCase(IToken tok, DatatypeCtor ctor, [Captured] List<BoundVar> arguments) {
    Contract.Requires(tok != null);
    Contract.Requires(ctor != null);
    Contract.Requires(cce.NonNullElements(arguments));
    this.tok = tok;
    this.Ctor = ctor;
    this.Arguments = arguments;
  }

  public IToken NameToken => tok;
  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations() {
    return new[] { Ctor };
  }
}

public class MatchStmt : Statement, ICloneable<MatchStmt> {
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Source != null);
    Contract.Invariant(cce.NonNullElements(Cases));
    Contract.Invariant(cce.NonNullElements(MissingCases));
  }

  private Expression source;
  private List<MatchCaseStmt> cases;
  public readonly MatchingContext Context;
  [FilledInDuringResolution] public readonly List<DatatypeCtor> MissingCases = new();
  public readonly bool UsesOptionalBraces;

  [FilledInDuringResolution]
  // TODO remove field?
  public MatchStmt OrigUnresolved;  // the resolver makes this clone of the MatchStmt before it starts desugaring it

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
      OrigUnresolved = original.OrigUnresolved;
    }
  }

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

  public List<MatchCaseStmt> Cases => cases;

  public override IEnumerable<INode> Children => new[] { Source }.Concat<INode>(Cases);

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

  public MatchCaseStmt(IToken tok, DatatypeCtor ctor, bool fromBoundVar, [Captured] List<BoundVar> arguments, [Captured] List<Statement> body, Attributes attrs = null)
    : base(tok, ctor, arguments) {
    Contract.Requires(tok != null);
    Contract.Requires(ctor != null);
    Contract.Requires(cce.NonNullElements(arguments));
    Contract.Requires(cce.NonNullElements(body));
    this.body = body;
    this.Attributes = attrs;
    this.FromBoundVar = fromBoundVar;
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

  public override IEnumerable<INode> Children => Arguments.Concat<INode>(new[] { body });

  public MatchCaseExpr(IToken tok, DatatypeCtor ctor, bool FromBoundVar, [Captured] List<BoundVar> arguments, Expression body, Attributes attrs = null)
    : base(tok, ctor, arguments) {
    Contract.Requires(tok != null);
    Contract.Requires(ctor != null);
    Contract.Requires(cce.NonNullElements(arguments));
    Contract.Requires(body != null);
    this.body = body;
    this.Attributes = attrs;
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
    return this.FillHole(new ForallCtx());
  }

  public virtual MatchingContext FillHole(MatchingContext curr) {
    return this;
  }
}

public class LitCtx : MatchingContext {
  public readonly LiteralExpr Lit;

  public LitCtx(LiteralExpr lit) {
    Contract.Requires(lit != null);
    this.Lit = lit;
  }

  public override string ToString() {
    return Printer.ExprToString(Lit);
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
    this.Id = id;
    this.Arguments = arguments;
  }

  public IdCtx(DatatypeCtor ctor) {
    List<MatchingContext> arguments = Enumerable.Repeat((MatchingContext)new HoleCtx(), ctor.Formals.Count).ToList();
    this.Id = ctor.Name;
    this.Arguments = arguments;
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
    return new IdCtx(this.Id, this.Arguments.ConvertAll<MatchingContext>(x => x.AbstractAllHoles()));
  }

  // Find the first (leftmost) occurrence of HoleCtx and replace it with curr
  // Returns false if no HoleCtx is found
  private bool ReplaceLeftmost(MatchingContext curr, out MatchingContext newContext) {
    var newArguments = new List<MatchingContext>();
    bool foundHole = false;
    int currArgIndex = 0;

    while (!foundHole && currArgIndex < this.Arguments.Count) {
      var arg = this.Arguments.ElementAt(currArgIndex);
      switch (arg) {
        case HoleCtx _:
          foundHole = true;
          newArguments.Add(curr);
          break;
        case IdCtx argId:
          MatchingContext newarg;
          foundHole = argId.ReplaceLeftmost(curr, out newarg);
          newArguments.Add(newarg);
          break;
        default:
          newArguments.Add(arg);
          break;
      }
      currArgIndex++;
    }

    if (foundHole) {
      while (currArgIndex < this.Arguments.Count) {
        newArguments.Add(this.Arguments.ElementAt(currArgIndex));
        currArgIndex++;
      }
    }

    newContext = new IdCtx(this.Id, newArguments);
    return foundHole;
  }

  public override MatchingContext FillHole(MatchingContext curr) {
    MatchingContext newContext;
    ReplaceLeftmost(curr, out newContext);
    return newContext;
  }
}
