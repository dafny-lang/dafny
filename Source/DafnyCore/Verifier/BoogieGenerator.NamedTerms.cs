using System;
using System.Collections.Generic;
using System.Linq;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  /// <summary>
  /// The variables that the translation of a quantifier binds to the terms that the matching-loop rewrite named in it
  /// ({:_named}), so that its triggers ({:_trigger}) can have a variable where they would have its term, which no
  /// trigger may contain. A variable is defined by its term's translation and replaces just that Boogie term, outside
  /// the binders of the term's variables, so the translation means the same whatever the term is.
  /// </summary>
  internal class NamedTerms {
    private readonly List<Expression> terms;
    public List<Bpl.Variable> Variables { get; }

    public NamedTerms(BoogieGenerator generator, Attributes attributes,
      Dictionary<IVariable, Expression> substMap = null) {
      terms = (Attributes.FindExpressions(attributes, "_named") ?? []).ConvertAll(term =>
        substMap == null ? term : Substitute(term, null, substMap));
      Variables = terms.ConvertAll(term => (Bpl.Variable)new Bpl.BoundVariable(term.Origin,
        new Bpl.TypedIdent(term.Origin, generator.CurrentIdGenerator.FreshId("_t#"), generator.TrType(term.Type))));
    }

    public List<Tuple<Bpl.Variable, Bpl.Expr>> VariablesAndDefinitions(ExpressionTranslator etran) {
      return terms.Select((term, i) => Tuple.Create(Variables[i],
        (Bpl.Expr)Bpl.Expr.Eq(new Bpl.IdentifierExpr(Variables[i].tok, Variables[i]), etran.TrExpr(term)))).ToList();
    }

    public Bpl.Expr Definitions(ExpressionTranslator etran) {
      return VariablesAndDefinitions(etran).Aggregate((Bpl.Expr)Bpl.Expr.True, (all, definition) => BplAnd(all, definition.Item2));
    }

    /// <summary>
    /// Replaces the terms in an expression that the translator translated with the variables
    /// </summary>
    public Bpl.Expr Replace(ExpressionTranslator etran, Bpl.Expr expr) {
      if (terms.Count == 0) {
        return expr;
      }
      var replacer = new Replacer(Translations(etran));
      var replaced = (Bpl.Expr)replacer.Visit(expr);
      return replacer.Replaced ? replaced : expr;
    }

    /// <summary>
    /// Replaces the terms in a trigger that the translator translated with the variables, and tells whether the trigger
    /// then is one for a quantifier of the bound variables, among them the variables: whether it mentions each of them,
    /// and has no term that is just a variable and no operation that no trigger may contain. A term whose translation is
    /// a bound variable leaves the trigger without it; a term whose translation is a whole term of the trigger, or an
    /// occurrence that the replacement misses, would leave a variable or an operation, which Boogie rejects.
    /// </summary>
    public bool Replace(ExpressionTranslator etran, List<Bpl.Expr> trigger, List<Bpl.Variable> bound) {
      if (terms.Count == 0) {
        return true;
      }
      var replacer = new Replacer(Translations(etran));
      for (var i = 0; i < trigger.Count; i++) {
        trigger[i] = (Bpl.Expr)replacer.Visit(trigger[i]);
      }
      var names = new VariableNameVisitor();
      var killers = new KillerFinder();
      trigger.ForEach(term => {
        names.Visit(term);
        killers.Visit(term);
      });
      return bound.All(variable => names.Names.Contains(variable.Name)) && !killers.Found &&
             !trigger.Exists(term => term is Bpl.IdentifierExpr);
    }

    private List<(Bpl.Expr Term, ISet<string> Names, Bpl.Variable Variable)> Translations(ExpressionTranslator etran) {
      return terms.Select((term, i) => {
        var translation = etran.TrExpr(term);
        var names = new VariableNameVisitor();
        names.Visit(translation);
        return (translation, (ISet<string>)names.Names, Variables[i]);
      }).ToList();
    }
  }

  /// <summary>
  /// Whether two Boogie expressions that are not resolved yet are the same term, up to the names of the variables that
  /// they bind, which bound maps from a's to b's. Function calls compare by name, as their functions are not resolved.
  /// </summary>
  private static bool SameTerm(Bpl.Expr a, Bpl.Expr b, Dictionary<string, string> bound = null) {
    bound ??= [];
    return (a, b) switch {
      (Bpl.LiteralExpr x, Bpl.LiteralExpr y) => Equals(x.Val, y.Val),
      (Bpl.IdentifierExpr x, Bpl.IdentifierExpr y) => bound.TryGetValue(x.Name, out var name)
        ? name == y.Name
        : x.Name == y.Name && x.Decl == y.Decl && !bound.ContainsValue(y.Name),
      (Bpl.NAryExpr x, Bpl.NAryExpr y) => SameFunction(x.Fun, y.Fun) && x.Args.Count == y.Args.Count &&
                                          x.Args.Zip(y.Args).All(args => SameTerm(args.First, args.Second, bound)),
      (Bpl.OldExpr x, Bpl.OldExpr y) => SameTerm(x.Expr, y.Expr, bound),
      (Bpl.BvExtractExpr x, Bpl.BvExtractExpr y) => x.Start == y.Start && x.End == y.End &&
                                                    SameTerm(x.Bitvector, y.Bitvector, bound),
      (Bpl.BvConcatExpr x, Bpl.BvConcatExpr y) => SameTerm(x.E0, y.E0, bound) && SameTerm(x.E1, y.E1, bound),
      (Bpl.BinderExpr x, Bpl.BinderExpr y) => x.GetType() == y.GetType() && x.TypeParameters.Count == 0 &&
                                              y.TypeParameters.Count == 0 &&
                                              Binding(bound, x.Dummies, y.Dummies) is { } inner &&
                                              SameTerm(x.Body, y.Body, inner),
      (Bpl.LetExpr x, Bpl.LetExpr y) => x.Rhss.Count == y.Rhss.Count &&
                                         x.Rhss.Zip(y.Rhss).All(rhss => SameTerm(rhss.First, rhss.Second, bound)) &&
                                         Binding(bound, x.Dummies, y.Dummies) is { } inner && SameTerm(x.Body, y.Body, inner),
      _ => false
    };
  }

  /// <summary>
  /// The map of the bound variables inside binders of these variables, if they are as many and of the same types
  /// </summary>
  private static Dictionary<string, string> Binding(Dictionary<string, string> bound, List<Bpl.Variable> a,
    List<Bpl.Variable> b) {
    if (a.Count != b.Count || a.Zip(b).Any(dummies => !Equals(dummies.First.TypedIdent.Type, dummies.Second.TypedIdent.Type))) {
      return null;
    }
    // b's variables hide those of enclosing binders with their names
    var inner = bound.Where(pair => !b.Exists(dummy => dummy.Name == pair.Value)).ToDictionary();
    foreach (var (x, y) in a.Zip(b)) {
      inner[x.Name] = y.Name;
    }
    return inner;
  }

  private static bool SameFunction(Bpl.IAppliable f, Bpl.IAppliable g) {
    return f is Bpl.FunctionCall call
      ? g is Bpl.FunctionCall other && call.FunctionName == other.FunctionName
      : f is Bpl.UnaryOperator or Bpl.BinaryOperator or Bpl.TypeCoercion or Bpl.MapSelect or Bpl.MapStore or Bpl.IfThenElse
          or Bpl.ArithmeticCoercion && Equals(f, g);
  }

  /// <summary>
  /// Replaces terms with variables, outside binders of variables that a term mentions
  /// </summary>
  private class Replacer : Bpl.Duplicator {
    private List<(Bpl.Expr Term, ISet<string> Names, Bpl.Variable Variable)> terms;
    public bool Replaced { get; private set; }

    public Replacer(List<(Bpl.Expr Term, ISet<string> Names, Bpl.Variable Variable)> terms) {
      this.terms = terms;
    }

    public override Bpl.Absy Visit(Bpl.Absy node) {
      if (node is Bpl.Expr expr) {
        foreach (var (term, _, variable) in terms) {
          if (SameTerm(term, expr)) {
            Replaced = true;
            return new Bpl.IdentifierExpr(expr.tok, variable);
          }
        }
      }
      return base.Visit(node);
    }

    // Identifiers may refer to a binder's variables themselves
    public override Bpl.BoundVariable VisitBoundVariable(Bpl.BoundVariable node) {
      return node;
    }

    public override Bpl.QuantifierExpr VisitQuantifierExpr(Bpl.QuantifierExpr node) {
      return Under(node.Dummies, () => base.VisitQuantifierExpr(node));
    }

    public override Bpl.Expr VisitBinderExpr(Bpl.BinderExpr node) {
      return Under(node.Dummies, () => base.VisitBinderExpr(node));
    }

    public override Bpl.Expr VisitLetExpr(Bpl.LetExpr node) {
      return Under(node.Dummies, () => base.VisitLetExpr(node));
    }

    private TResult Under<TResult>(List<Bpl.Variable> dummies, Func<TResult> visit) {
      var outer = terms;
      terms = terms.Where(term => !dummies.Exists(dummy => term.Names.Contains(dummy.Name))).ToList();
      var result = visit();
      terms = outer;
      return result;
    }
  }

  /// <summary>
  /// Finds an operation that no trigger may contain
  /// </summary>
  private class KillerFinder : Bpl.ReadOnlyVisitor {
    public bool Found { get; private set; }

    public override Bpl.Expr VisitNAryExpr(Bpl.NAryExpr node) {
      Found |= node.Fun is Bpl.UnaryOperator or Bpl.BinaryOperator or Bpl.IfThenElse or Bpl.ArithmeticCoercion;
      return base.VisitNAryExpr(node);
    }
  }
}
