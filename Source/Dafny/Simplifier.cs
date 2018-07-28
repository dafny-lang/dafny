using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using System.Reflection;
using System.Text;

namespace Microsoft.Dafny {

  using SubstMap = Dictionary<IVariable, Expression>;
  using TypeSubstMap = Dictionary<TypeParameter, Type>;

  // TODO: Figure out how to use a Nullable constraint on R in ExpressionVisitor
  public abstract class Option<T> {
  }

  public class Some<T>: Option<T> {
    public T val;
    public Some(T val) {
      this.val = val;
    }
  }

  public class None<T>: Option<T> {
    public None() {

    }
  }

  // A generic expression visitor parameterized in result and state type
  public class ExpressionVisitor<R, S> {

    internal Func<Expression, R> defaultRet;
    public ExpressionVisitor(Func<Expression, R> defaultRet) {
      this.defaultRet = defaultRet;
    }

    public virtual R Visit(Expression e, S st) {
      Option<R> res = VisitOneExpr(e, st);
      if (res is Some<R>) {
        return ((Some<R>)res).val;
      }
      // A hacky way to do double dispatch without enumerating all the subclasses
      // of Expression:
      var method = from m in GetType().GetMethods()
        where m.Name == "Visit"
        && m.GetParameters().Length==2
        && e.GetType().IsAssignableFrom(m.GetParameters()[0].ParameterType)
        && typeof(S).IsAssignableFrom(m.GetParameters()[1].ParameterType)
        && m.ReturnType == typeof(R)
        select m;
      var methods = method.ToList();
      if (methods.Count() == 0) {
        // Console.WriteLine("No suitable method for expression of type: " + e.GetType());
        return this.defaultRet(e);
      } else if (methods.Count() > 1) {
        throw new System.ArgumentException("More than one visit method for: " + e.GetType());
      } else {
        try {
          return (R) methods[0].Invoke(this, new object[]{e, st});
        } catch(TargetInvocationException tie) {
          throw tie.InnerException;
        }
      }
    }

    public virtual R Visit(ConcreteSyntaxExpression e, S st) {
      // For the purposes of the simplifier we only want to operate
      // on resolved expressions.
      return Visit(e.ResolvedExpression, st);
    }

    public virtual Option<R> VisitOneExpr(Expression e, S st) {
      return new None<R>();
    }
  }

  // A visitor for transforming expressions. Since expression fields are
  // readonly, we need to rebuild an expression as soon as we want to change any
  // part of it.
  public class ExpressionTransformer: ExpressionVisitor<Expression, object>
  {
    public ExpressionTransformer(Func<Expression, Expression> defaultRet):
      base(defaultRet) {
    }

    public virtual Expression Visit(BinaryExpr e, object st) {
      var lhs = Visit(e.E0, st);
      var rhs = Visit(e.E1, st);
      if (lhs != e.E0 || rhs != e.E1) {
        var res = new BinaryExpr(e.tok, e.ResolvedOp, lhs, rhs);
        res.Type = e.Type;
        return res;
      }
      return e;
    }

    public override Expression Visit(ConcreteSyntaxExpression e, object st) {
      var newRes = Visit(e.ResolvedExpression, st);
      e.ResolvedExpression = newRes;
      return e;
    }

    public virtual Expression Visit(UnaryOpExpr e, object st) {
      var eNew = Visit(e.E, st);
      if (e != eNew) {
        var res = new UnaryOpExpr(e.tok, e.Op, eNew);
        res.Type = e.Type;
        return res;
      }
      return e;
    }

    public virtual Expression Visit(TernaryExpr e, object st) {
      var e0 = Visit(e.E0, st);
      var e1 = Visit(e.E1, st);
      var e2 = Visit(e.E2, st);
      if (e0 != e.E0 || e1 != e.E1 || e2 != e.E2) {
        var res = new TernaryExpr(e.tok, e.Op, e0, e1, e2);
        res.Type = e.Type;
        return res;
      }
      return e;
    }

    public virtual Expression Visit(ITEExpr e, object st) {
      var e0 = Visit(e.Test, st);
      var e1 = Visit(e.Thn, st);
      var e2 = Visit(e.Els, st);
      if (e0 != e.Test || e1 != e.Thn || e2 != e.Els) {
        var res = new ITEExpr(e.tok, e.IsBindingGuard, e0, e1, e2);
        res.Type = e.Type;
        return res;
      }
      return e;
    }

    public virtual Expression Visit(FunctionCallExpr e, object st) {
      List<Expression> newArgs = new List<Expression>();
      bool changed = false;
      foreach (var arg in e.Args) {
        var newArg = Visit(arg, st);
        if (newArg != arg) {
          changed = true;
        }
        newArgs.Add(newArg);
      }
      if (changed) {
        var res = new FunctionCallExpr(e.tok, e.Name, e.Receiver, e.OpenParen, newArgs);
        res.Type = e.Type;
        res.TypeArgumentSubstitutions = e.TypeArgumentSubstitutions;
        res.CoCall = e.CoCall;
        res.Function = e.Function;
        res.CoCallHint = e.CoCallHint;
        return res;
      }
      return e;
    }

    public virtual Expression Visit(IdentifierExpr e, object st) {
      return e;
    }

    public virtual Expression Visit(DatatypeValue dv, object st) {
      List<Expression> newArgs = new List<Expression>();
      bool changed = false;
      foreach (var arg in dv.Arguments) {
        var newArg = Visit(arg, st);
        if (newArg != arg) {
          changed = true;
        }
        newArgs.Add(newArg);
      }
      if (changed) {
        var res = new DatatypeValue(dv.tok, dv.DatatypeName, dv.MemberName, newArgs);
        res.Type = dv.Type;
        res.Ctor = dv.Ctor;
        res.InferredTypeArgs = dv.InferredTypeArgs;
        res.IsCoCall = dv.IsCoCall;
        return res;
      }
      return dv;
    }
  }

  public class UnificationError: Exception
  {
    public UnificationError() { }

    public UnificationError(string message)
      : base(message)
    {
    }

    public UnificationError(string message, Exception inner)
      : base(message, inner)
    {
    }

    public UnificationError(Expression lhs, Expression rhs) :
      this("Can't unify: ", lhs, rhs)
    {
    }

    public UnificationError(String prefix, Expression lhs, Expression rhs) :
      this(prefix + Printer.ExprToString(lhs) + " and " + Printer.ExprToString(rhs))
    {
    }
  }

  // Visitor for trying to unify an expression with a pattern
  // Throws a UnificationError if unification fails.
  internal class UnificationVisitor : ExpressionVisitor<object, Expression>
  {

    // Not used yet; need to keep track of bound variables if we want
    // to support LetExprs
    internal Stack<HashSet<IVariable>> boundVars;
    internal SubstMap map = new Dictionary<IVariable, Expression>();
    internal Dictionary<TypeParameter, Type> typeMap =
      new Dictionary<TypeParameter, Type>();

    public UnificationVisitor()
      : base(e => throw new UnificationError("Unhandled expression type: " + e.GetType()))
    {
      this.boundVars = new Stack<HashSet<IVariable>>();
    }

    public SubstMap GetSubstMap {
      get { return map; }
    }

    public TypeSubstMap GetTypeSubstMap {
      get { return typeMap; }
    }

    public override Option<object> VisitOneExpr(Expression pattern, Expression target) {
      return new None<object>();
    }

    internal bool IsBound(IVariable x) {
      foreach (var hs in boundVars) {
        if (hs.Contains(x)) {
          return true;
        }
      }
      return false;
    }

    public object Visit(TernaryExpr e, Expression target) {
      if (!(target is TernaryExpr)) {
        throw new UnificationError(e, target);
      }
      var ttarget = (TernaryExpr)target;
      Visit(e.E0, ttarget.E0);
      Visit(e.E1, ttarget.E1);
      Visit(e.E2, ttarget.E2);
      return null;
    }

    internal void AddBinding(IVariable x, Expression e) {
      if (map.ContainsKey(x)) {
        var val = map[x];
        if (!val.Equals(e)) {
          throw new UnificationError("Conflicting binding for " + x + ": " + val + " & " + e);
        }
      } else {
        map.Add(x, e);
      }
    }

    internal void AddTypeBinding(TypeParameter tp, Type t) {
      if (typeMap.ContainsKey(tp)) {
        var val = typeMap[tp];
        if (!val.Equals(t)) {
          throw new UnificationError("Conflicting type binding for " + tp + ": " + val + " & " + t);
        }
      } else {
        typeMap.Add(tp, t);
      }
    }

    public object Visit(IdentifierExpr e, Expression target) {
      if (IsBound(e.Var)) {
        if (!(target is IdentifierExpr)) {
          throw new UnificationError(e, target);
        }
        var itarget = (IdentifierExpr) target;
        if (!itarget.Var.Equals(e.Var)) {
          throw new UnificationError(e, target);
        }
      } else {
        AddBinding(e.Var, target);
      }
      return null;
    }

    public object Visit(ITEExpr e, Expression target) {
      if (!(target is ITEExpr)) {
        throw new UnificationError(e, target);
      }
      var targetITE = (ITEExpr)target;
      Visit(e.Test, targetITE.Test);
      Visit(e.Thn, targetITE.Thn);
      Visit(e.Els, targetITE.Els);
      return null;
    }

    // FIXME: find a more efficient and idiomatic C# way to do this:
    private static bool SameKeys<K, V>(Dictionary<K, V> d1, Dictionary<K, V> d2) {
      foreach (var key in d1.Keys) {
        if (!d2.ContainsKey(key))
          return false;
      }
      foreach (var key in d2.Keys) {
        if (!d1.ContainsKey(key))
          return false;
      }
      return true;
    }

    public object Visit(FunctionCallExpr fc, Expression target) {
      if (!(target is FunctionCallExpr)) {
        throw new UnificationError("Target not a function(" + target.GetType() + ")",
                                    fc, target);
      }
      var fctarget = (FunctionCallExpr)target;
      if (fc.Args.Count != fctarget.Args.Count ||
          (!fc.Function.Equals(fctarget.Function))) {
        throw new UnificationError("Different function or argument count: ", fc, target);
      }
      if (!SameKeys(fc.TypeArgumentSubstitutions, fctarget.TypeArgumentSubstitutions)) {
        // FIXME: check if this can actually happen, maybe this check is not needed
        throw new UnificationError("Different type parameters to function: ", fc, target);
      }
      foreach (var key in fctarget.TypeArgumentSubstitutions.Keys) {
        var lhsType = fc.TypeArgumentSubstitutions[key];
        if ((lhsType is UserDefinedType) && ((UserDefinedType)lhsType).ResolvedParam != null) {
          var ut = (UserDefinedType)lhsType;
          AddTypeBinding(ut.ResolvedParam, fctarget.TypeArgumentSubstitutions[key]);
        } else {
          // FIXME: proper using unification procedure for types.
          throw new UnificationError("Only fully polymorphic simplification lemmas supported at the moment", fc, fctarget);
        }
      }
      for (int i = 0; i < fc.Args.Count; i++) {
        Visit(fc.Args[i].Resolved, fctarget.Args[i].Resolved);
      }
      return null;
    }

    public object Visit(BinaryExpr be, Expression target) {
      if (!(target is BinaryExpr)) {
        throw new UnificationError(be, target);
      }
      var btarget = (BinaryExpr)target;
      if (!btarget.ResolvedOp.Equals(btarget.ResolvedOp)) {
        throw new UnificationError(be, target);
      }
      Visit(be.E0, btarget.E0);
      Visit(be.E1, btarget.E1);
      return null;
    }

    public object Visit(LiteralExpr le, Expression target) {
      if (!(target is LiteralExpr)) {
        throw new UnificationError(le, target);
      }
      if (!le.Value.Equals(((LiteralExpr)target).Value)) {
        throw new UnificationError(le, target);
      }
      return null;
    }

    public object Visit(UnaryOpExpr ue, Expression target) {
      if (!(target is UnaryOpExpr)) {
        throw new UnificationError(ue, target);
      }
      UnaryOpExpr utarget = (UnaryOpExpr) target;
      if (!ue.Op.Equals(utarget.Op)) {
        throw new UnificationError("Different unary operator: ", ue, target);
      }
      Visit(ue.E, utarget.E);
      return null;
    }

    public object Visit(DatatypeValue dv, Expression target) {
      if (!(target is DatatypeValue)) {
        throw new UnificationError(dv, target);
      }
      var dtarget = (DatatypeValue) target;
      if (!dv.Ctor.Equals(dtarget.Ctor)) {
        throw new UnificationError("Different constructors: ", dv, target);
      }
      if (dv.Arguments.Count != dtarget.Arguments.Count) {
        throw new UnificationError("Different argument counts: ", dv, target);
      }
      if (dv.InferredTypeArgs.Count != dtarget.InferredTypeArgs.Count) {
        throw new UnificationError("Different number of type arguments: ", dv, target);
      }
      for (int i = 0; i < dv.Arguments.Count; i++) {
        Visit(dv.Arguments[i].Resolved, dtarget.Arguments[i].Resolved);
      }
      return null;
    }

    public override object Visit(ConcreteSyntaxExpression e, Expression target) {
      return Visit(e.Resolved, target.Resolved);
    }
  }

  public class SimplifyingRewriter : IRewriter {
    internal SimplifyingRewriter(ErrorReporter reporter) : base(reporter) {
      Contract.Requires(reporter != null);
    }

    protected HashSet<Function> simplifierFuncs = new HashSet<Function>();
    protected HashSet<Lemma> simplifierLemmas = new HashSet<Lemma>();

    internal void FindSimplificationCallables(ModuleDefinition m) {
      foreach (var decl in ModuleDefinition.AllCallables(m.TopLevelDecls)) {
        if (decl is Function) {
          Function f = (Function) decl;
          if (Attributes.Contains(f.Attributes, "simp")) {
            simplifierFuncs.Add(f);
          }
        }
        else if (decl is Lemma) {
          Lemma l = (Lemma) decl;
          if (Attributes.Contains(l.Attributes, "simp")) {
            if (l.Ens.Count() == 1 &&
                l.Ens[0].E is BinaryExpr &&
                ((BinaryExpr)l.Ens[0].E).Op == BinaryExpr.Opcode.Eq) {
              simplifierLemmas.Add(l);
            } else {
              // Console.WriteLine("Simplification lemma not a single equality: " + l);
            }
          }
        }
      }
    }

    // FIXME: use Dafny's logging functions instead
    public static void DebugMsg(String s) {
      Console.WriteLine(s);
    }

    public static void DebugExpression(String prefix, Expression e, bool subexps=false) {
      Console.WriteLine(prefix + Printer.ExprToString(e) + "[" + e.GetType() + "]");
      if (e is FunctionCallExpr) {
        var fc = (FunctionCallExpr)e;
        foreach (var item in fc.TypeArgumentSubstitutions) {
          Console.WriteLine(item.Key.FullName() + "] " + item.Key.GetHashCode() + "] |-> " + item.Value + "[" + item.Value.GetType() + "]");
          if (item.Value is UserDefinedType) {
            var ut = (UserDefinedType) item.Value;
            Console.WriteLine(prefix + "; " + item.Value + " is user defined; ResolvedParam: " + ut.ResolvedParam +
                              "[" + ut.ResolvedParam.GetHashCode() + "]");
          }
        }
      }
      if (subexps) {
        foreach (var subexp in e.SubExpressions) {
          DebugExpression("\t" + prefix, subexp.Resolved, subexps);
        }
      }
    }

    // Returns null iff unification failed.
    internal static UnificationVisitor UnifiesWith(Expression target, Expression pattern) {
      try {
        var uf = new UnificationVisitor();
        uf.Visit(pattern.Resolved, target);
        return uf;
      } catch(UnificationError) {
        return null;
      }
    }

    internal class SimplificationVisitor: ExpressionTransformer
    {
      HashSet<Lemma> simplifierLemmas;
      public SimplificationVisitor(HashSet<Lemma> simplifierLemmas) :
        base(e => e) {
        this.simplifierLemmas = simplifierLemmas;
      }

      public override Option<Expression> VisitOneExpr(Expression e, object st) {
        foreach (var simpLem in simplifierLemmas) {
          // if (simpLem.TypeArgs.Count
          // TODO: insert contract calls that lemma is equality
          var eq = (BinaryExpr)simpLem.Ens[0].E;
          var uv = UnifiesWith(e.Resolved, eq.E0.Resolved);
          if (uv != null) {
            // DebugMsg(e.Resolved + " unifies with " + eq.E0.Resolved);
            // FIXME: check that we don't need the receiverParam argument
            var res = Translator.Substitute(eq.E1.Resolved, null, uv.GetSubstMap, uv.GetTypeSubstMap);
            return new Some<Expression>(res);
          }
        }
        return new None<Expression>();
      }

    }


    internal class SimplifyInExprVisitor : ExpressionTransformer
    {
      HashSet<Function> simplifierFuncs;
      HashSet<Lemma> simplifierLemmas;

      public SimplifyInExprVisitor(HashSet<Function> simplifierFuncs, HashSet<Lemma> simplifierLemmas) :
        base(e => e) {
        this.simplifierFuncs = simplifierFuncs;
        this.simplifierLemmas = simplifierLemmas;
      }

      internal Expression Simplify(Expression e) {
        var expr = e;
        // Keep trying to simplify until we (hopefully) reach a fixpoint
        // FIXME: add parameter to control maximum simplification steps?
        while(true) {
          var sv = new SimplificationVisitor(simplifierLemmas);
          var simplified = sv.Visit(expr, null);
          if (simplified == expr) {
            break;
          } else {
            expr = simplified;
          }
        }
        return expr;
      }

      public override Expression Visit(FunctionCallExpr fc, object st) {
        if (simplifierFuncs.Contains(fc.Function)) {
          //DebugMsg("Found call to simplifier: " + Printer.ExprToString(fc));
          List<Expression> newArgs = new List<Expression>();
          foreach (var arg in fc.Args) {
            newArgs.Add(Simplify(arg));
          }
          var res = new FunctionCallExpr(fc.tok, fc.Name, fc.Receiver, fc.OpenParen, newArgs);
          res.Type = fc.Type;
          res.Function = fc.Function;
          res.TypeArgumentSubstitutions = fc.TypeArgumentSubstitutions;
          res.CoCall = fc.CoCall;
          res.CoCallHint = fc.CoCallHint;
          // DebugExpression("Simplification result: ", res, true);
          return res;
        } else {
          return fc;
        }
      }
    }

    // FIXME: rewrite this using a visitor
    internal Expression SimplifyInExpr(Expression e) {
      var sv = new SimplifyInExprVisitor(simplifierFuncs, simplifierLemmas);
      return sv.Visit(e, null);
    }

    internal void SimplifyCalls(ModuleDefinition m) {
      foreach (Function fun in ModuleDefinition.AllFunctions(m.TopLevelDecls)) {
        if (fun.Body is ConcreteSyntaxExpression) {
          ((ConcreteSyntaxExpression)fun.Body).ResolvedExpression = SimplifyInExpr(fun.Body.Resolved);
        }
      }
    }

    internal override void PostResolve(ModuleDefinition m) {
      FindSimplificationCallables(m);
      SimplifyCalls(m);
    }
  }
}
