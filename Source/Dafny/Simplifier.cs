using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using System.Reflection;
using System.Text;
using Microsoft.Boogie;

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

  public class TypeVisitor<R, S> {
    internal Func<Type, R> defaultRet;
    public TypeVisitor(Func<Type, R> defaultRet) {
      this.defaultRet = defaultRet;
    }
    public virtual R Visit(Type t, S st) {
      var res = VisitOneType(t, st);
      if (res is Some<R>) {
        return ((Some<R>)res).val;
      }
      var method = from m in GetType().GetMethods()
        where m.Name == "Visit"
        && m.GetParameters().Length==2
        && t.GetType().IsAssignableFrom(m.GetParameters()[0].ParameterType)
        && typeof(S).IsAssignableFrom(m.GetParameters()[1].ParameterType)
        && m.ReturnType == typeof(R)
        select m;
      var methods = method.ToList();
      if (methods.Count() == 0) {
        // Console.WriteLine("No suitable method for expression of type: " + e.GetType());
        return this.defaultRet(t);
      } else if (methods.Count() > 1) {
        throw new System.ArgumentException("More than one visit method for: " + t.GetType());
      } else {
        try {
          return (R) methods[0].Invoke(this, new object[]{t, st});
        } catch(TargetInvocationException tie) {
          throw tie.InnerException;
        }
      }
    }

    public virtual Option<R> VisitOneType(Type t, S st) {
      return new None<R>();
    }

    public virtual R Visit(InferredTypeProxy itp, S st) {
      return Visit(itp.NormalizeExpandKeepConstraints(), st);
    }
  }

  // A generic expression visitor parameterized in result and state type
  public class ExpressionVisitor<R, S> {

    internal Func<Expression, R> defaultRet;
    // This is a bit of an ad-hoc extension to handle StmtExprs in the
    // unification visitor to avoid having to call this function on each
    // recursive call.
    internal Func<S, S> transformState;

    public ExpressionVisitor(Func<Expression, R> defaultRet, Func<S, S> transformState=null) {
      this.defaultRet = defaultRet;
      if (transformState == null) {
        this.transformState = (s) => s;
      } else {
        this.transformState = transformState;
      }
    }

    public virtual R Visit(Expression e, S st) {
      Option<R> res = VisitOneExpr(e, transformState(st));
      if (res is Some<R>) {
        return ((Some<R>)res).val;
      }
      if (e is ConcreteSyntaxExpression) {
        if (((ConcreteSyntaxExpression)e).ResolvedExpression == null) {
          return defaultRet(e);
        }
        return Visit(e.Resolved, transformState(st));
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
          return (R) methods[0].Invoke(this, new object[]{e, transformState(st)});
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

    public virtual Expression Visit(MemberSelectExpr e, object st) {
      var newObj = Visit(e.Obj, st);
      if (newObj != e.Obj) {
        var res = new MemberSelectExpr(e.tok, newObj, (Field)e.Member);
        res.Type = e.Type;
        res.TypeApplication = e.TypeApplication;
        return res;
      } else {
        return e;
      }
    }

    public virtual Expression Visit(StmtExpr e, object st) {
      // FIXME:
      // For now, we don't visit the statement part, since this isn't really
      // necessary for the simplification cases we care about... I hope
      var newE = Visit(e.E, st);
      if (newE != e.E) {
        var res = new StmtExpr(e.tok, e.S, newE);
        res.Type = e.Type;
        return res;
      } else {
        return e;
      }
    }
  }

  public class StatementVisitor<R, S>
  {
    internal Func<Statement, R> defaultRet;
    public StatementVisitor() :
      this(s => default(R)) {
    }

    public StatementVisitor(Func<Statement, R> defaultRet) {
      this.defaultRet = defaultRet;
    }

    public R Visit(Statement s, S st) {
      Contract.Assert(s != null);
      var res = VisitOneStmt(s, st);
      if (res is Some<R>) {
        return ((Some<R>)res).val;
      }
      var method = from m in GetType().GetMethods()
        where m.Name == "Visit"
        && m.GetParameters().Length==2
        && s.GetType().IsAssignableFrom(m.GetParameters()[0].ParameterType)
        && typeof(S).IsAssignableFrom(m.GetParameters()[1].ParameterType)
        && m.ReturnType == typeof(R)
        select m;
      Contract.Assert(method != null);
      var methods = method.ToList();
      if (methods.Count() == 0) {
        // Console.WriteLine("No suitable method for statement of type: " + s.GetType());
        return this.defaultRet(s);
      } else if (methods.Count() > 1) {
        throw new System.ArgumentException("More than one visit method for: " + s.GetType());
      } else {
        try {
          return (R) methods[0].Invoke(this, new object[]{s, st});
        } catch(TargetInvocationException tie) {
          // Since we use UnificationErrors to signal unification failure we
          // need to rethrow it here for callers to be able to catch it.
          if (tie.InnerException is UnificationError) {
            throw tie.InnerException;
          }
          // Otherwise it's useful to get the original exception for debugging
          // purposes
          throw tie;
        }
      }
    }

    public virtual Option<R> VisitOneStmt(Statement s, S st) {
      return new None<R>();
    }
  }

  public class StatementTransformer: StatementVisitor<Statement, object>
  {
    ExpressionTransformer et = null;
    public StatementTransformer(ExpressionTransformer et) :
      base(s => s)
    {
      this.et = et;
    }
    public virtual Statement Visit(IfStmt s, object st) {
      Expression newGuard = VisitExpr(s.Guard, st);
      var newThn = Visit(s.Thn, st);
      Contract.Assert(newThn is BlockStmt);
      Statement newEls = null;
      if (s.Els != null) {
        newEls = Visit(s.Els, st);
      }
      if (newGuard != s.Guard || newThn != s.Thn || newEls != s.Els) {
        var res = new IfStmt(s.Tok, s.EndTok, s.IsBindingGuard, newGuard, (BlockStmt)newThn, newEls);
        CopyCommon(res, s);
        return res;
      }
      return s;
    }

    internal void CopyCommon(Statement to, Statement fro) {
      to.IsGhost = fro.IsGhost;
      to.Labels = fro.Labels;
      to.Attributes = fro.Attributes;
    }

    public virtual Statement Visit(VarDeclStmt s, object st) {
      var newUpd = Visit(s.Update, st);
      Contract.Assert(newUpd is ConcreteUpdateStatement);
      if (newUpd != s.Update) {
        var res = new VarDeclStmt(s.Tok, s.EndTok, s.Locals, (ConcreteUpdateStatement)newUpd);
        CopyCommon(res, s);
        return res;
      } else {
        return s;
      }
    }

    internal Expression VisitExpr(Expression e, object st) {
      SimplifyingRewriter.DebugExpression("StatementTransformer: visiting expression: ", e);
      if (et != null) {
        return et.Visit(e, st);
      } else {
        return e;
      }
    }

    public virtual AssignmentRhs VisitAssignmentRhs(AssignmentRhs rhs, object st) {
      AssignmentRhs newRhs = rhs;
      if (rhs is ExprRhs) {
        var erhs = (ExprRhs) rhs;
        var newRhsExpr = VisitExpr(erhs.Expr, st);
        newRhs = new ExprRhs(newRhsExpr);
      }
      // FIXME: handle the other cases for AssignmentRhs
      return newRhs;
    }

    // FIXME: should probably move this to ExpressionVisitor
    internal virtual List<Expression> VisitExprs(List<Expression> exprs, object st, ref bool changed) {
      List<Expression> newExprs = new List<Expression>();
      foreach (var expr in exprs) {
        var newExpr = VisitExpr(expr, st);
        if (newExpr != expr) { changed = true; }
        newExprs.Add(newExpr);
      }
      return newExprs;
    }

    public virtual Statement Visit(UpdateStmt s, object st) {
      bool changed = false;
      List<Expression> newLhss = VisitExprs(s.Lhss, st, ref changed);
      Contract.Assert(newLhss.Count == s.Lhss.Count);
      List<AssignmentRhs> newRhss = new List<AssignmentRhs>();
      List<Statement> newResolved = VisitStmts(s.ResolvedStatements, st, ref changed);
      foreach (var rhs in s.Rhss) {
        var newRhs = VisitAssignmentRhs(rhs, st);
        if (newRhs != rhs) {
          changed = true;
        }
        newRhss.Add(newRhs);
      }
      Contract.Assert(newRhss.Count == s.Rhss.Count);
      if (changed) {
        var res = new UpdateStmt(s.Tok, s.EndTok, newLhss, newRhss, s.CanMutateKnownState);
        CopyCommon(res, s);
        foreach (var resolved in newResolved) {
          res.ResolvedStatements.Add(resolved);
        }
        return res;
      }
      return s;
    }

    public virtual Statement Visit(AssignStmt s, object st) {
      var newLhs = VisitExpr(s.Lhs, st);
      var newRhs = VisitAssignmentRhs(s.Rhs, st);
      if (newLhs != s.Lhs || newRhs != s.Rhs) {
        var res = new AssignStmt(s.Tok, s.EndTok, newLhs, newRhs);
        CopyCommon(res, s);
        return res;
      }
      return s;
    }

    public virtual Statement Visit(PrintStmt s, object st) {
      bool changed = false;
      List<Expression> newArgs = VisitExprs(s.Args, st, ref changed);
      if (changed) {
        var res = new PrintStmt(s.Tok, s.EndTok, newArgs);
        CopyCommon(res, s);
        return res;
      } else {
        return s;
      }
    }

    public virtual Statement Visit(AssumeStmt s, object st) {
      var newExpr = VisitExpr(s.Expr, st);
      if (newExpr != s.Expr) {
        var res = new AssumeStmt(s.Tok, s.EndTok, newExpr, s.Attributes);
        CopyCommon(res, s);
        return res;
      } else {
        return s;
      }
    }

    public virtual Statement Visit(AssertStmt s, object st) {
      Contract.Assert(s != null);
      Contract.Assert(s.Expr != null);
      var newExpr = VisitExpr(s.Expr, st);
      BlockStmt newProof;
      if (s.Proof == null) {
        newProof = null;
      } else {
        var np = Visit(s.Proof, st);
        Contract.Assert(np is BlockStmt);
        newProof = (BlockStmt)np;
      }
      if (newExpr != s.Expr || newProof != s.Proof) {
        var res = new AssertStmt(s.Tok, s.EndTok, newExpr, newProof, s.Attributes);
        CopyCommon(res, s);
        return res;
      } else {
        return s;
      }
    }

    internal virtual List<Statement> VisitStmts(List<Statement> stmts, object st, ref bool changed) {
      List<Statement> newStmts = new List<Statement>();
      foreach (var stmt in stmts) {
        var newStmt = Visit(stmt, st);
        if (newStmt != stmt) { changed = true; }
        newStmts.Add(newStmt);
      }
      return newStmts;
    }

    public virtual Statement Visit(BlockStmt s, object st) {
      Contract.Assert(s != null);
      Contract.Assert(s.Body != null);
      bool changed = false;
      var newStmts = VisitStmts(s.Body, st, ref changed);
      if (changed) {
        var res = new BlockStmt(s.Tok, s.EndTok, newStmts);
        CopyCommon(res, s);
        return res;
      } else {
        return s;
      }
    }

    public virtual Statement Visit(CallStmt s, object st) {
      bool changed = false;
      List<Expression> newLhss = VisitExprs(s.Lhs, st, ref changed);
      List<Expression> newArgs = VisitExprs(s.Args, st, ref changed);
      // FIXME: visit memberselectexpr as well
      if (changed) {
        var res = new CallStmt(s.Tok, s.EndTok, newLhss, s.MethodSelect, newArgs);
        CopyCommon(res, s);
        return res;
      } else {
        return s;
      }
    }

    public virtual Statement Visit(ForallStmt s, object st) {
      // TODO: transform ensures/requires clauses as well
      var newBody = Visit(s.Body, st);
      if (newBody != s) {
        var res = new ForallStmt(s.Tok, s.EndTok, s.BoundVars, s.Attributes, s.Range, s.Ens, newBody);
        CopyCommon(res, s);
        res.CanConvert = s.CanConvert;
        res.Bounds = s.Bounds;
        res.Kind = s.Kind;
        res.ForallExpressions = s.ForallExpressions;
        return res;
      } else {
        return s;
      }
    }

    public override Option<Statement> VisitOneStmt(Statement s, object st) {
      SimplifyingRewriter.DebugMsg($"Visiting statement {Printer.StatementToString(s)}");
      return new None<Statement>();
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

  public class TypeUnificationError: UnificationError
  {
    public TypeUnificationError(String msg):
      base(msg) {
    }

    public TypeUnificationError(String prefix, Type pattern, Type target):
      base(prefix + ": " + pattern + ", " + target)
    {
    }

    public TypeUnificationError(Type pattern, Type target):
      base("Can't unify " + target + " with pattern " + pattern)
    {

    }
  }

  internal class TypeUnifier : TypeVisitor<object, Type>
  {
    Dictionary<TypeParameter, Type> typeMap;

    public TypeUnifier(Dictionary<TypeParameter, Type> typeMap)
      : base(e => throw new TypeUnificationError("Unhandled type: " + e))
    {
      this.typeMap = typeMap;
    }

    internal void UnifyTypeArgs(Type t, Type target) {
      if (t.TypeArgs.Count != target.TypeArgs.Count) {
        throw new TypeUnificationError("Types have different number of type arguments",
                                       t, target);
      }
      for (int i = 0; i < t.TypeArgs.Count; i++) {
        Visit(t.TypeArgs[i], target.TypeArgs[i]);
      }
    }

    public override Option<object> VisitOneType(Type t, Type target) {
      if (t is UserDefinedType) {
        var ut = (UserDefinedType)t;
        if (ut.ResolvedParam != null) {
          // We don't need to unify the type arguments if the pattern is a
          // type parameter
          return new None<object>();
        }
      }
      UnifyTypeArgs(t, target);
      return new None<object>();
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

    public object Visit(UserDefinedType t, Type target) {
      if (t.ResolvedParam != null) {
        AddTypeBinding(t.ResolvedParam, target);
      } else {
        Contract.Assert(t.ResolvedClass != null);
        if (!(target is UserDefinedType)) {
          throw new TypeUnificationError(t, target);
        }
        var ut = (UserDefinedType) target;
        if (ut.ResolvedClass == null || !t.ResolvedClass.Equals(ut.ResolvedClass)) {
          throw new TypeUnificationError(t, target);
        }
      }
      return null;
    }

    public object Visit(IntType bt, Type target) {
      if (!target.Equals(bt)) {
        throw new TypeUnificationError(bt, target);
      }
      return null;
    }

    public object Visit(RealType bt, Type target) {
      if (!target.Equals(bt)) {
        throw new TypeUnificationError(bt, target);
      }
      return null;
    }

    public object Visit(CharType bt, Type target) {
      if (!target.Equals(bt)) {
        throw new TypeUnificationError(bt, target);
      }
      return null;
    }

    public object Visit(BoolType bt, Type target) {
      if (!target.Equals(bt)) {
        throw new TypeUnificationError(bt, target);
      }
      return null;
    }

    public object Visit(CollectionType ct, Type target) {
      if ((ct is SetType) && !(target is SetType)) {
        throw new TypeUnificationError(ct, target);
      }
      else if ((ct is SeqType) && !(target is SeqType)) {
        throw new TypeUnificationError(ct, target);
      }
      else if ((ct is MapType) && !(target is MapType)) {
        throw new TypeUnificationError(ct, target);
      }
      else if ((ct is MultiSetType) && !(target is MultiSetType)) {
        throw new TypeUnificationError(ct, target);
      }
      return null;
    }
  }

  // FIXME: We may want to move this to DafnyAst if needed by another class
  // as well.
  public class ExpressionEqualityVisitor: ExpressionVisitor<bool, Expression>
  {
    public ExpressionEqualityVisitor(bool def): base(e => def) {
    }

    public bool Visit(LiteralExpr e, Expression rhs) {
      if (!(rhs is LiteralExpr)) { return false; }
      return ((LiteralExpr)rhs).Value.Equals(e.Value);
    }

    // FIXME: handle other cases

    public override Option<bool> VisitOneExpr(Expression e, Expression rhs) {
      // If they're the same reference, they are definitely equal:
      if (e.Equals(rhs)) {
        return new Some<bool>(true);
      }
      return new None<bool>();
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

    // I'm not sure if we need to do more here to take the statement part of
    // a StmtExpr into account when rewriting; currently we just drop
    // the statement part in unification, since the patterns (i.e. the RHS of
    // simplification rules) will probably never contain StmtExprs anyway.
    public static Expression UnwrapStmtExpr(Expression e) {
      if (e is StmtExpr) {
        return UnwrapStmtExpr(((StmtExpr)e).E);
      } else {
        return e;
      }
    }

    public UnificationVisitor()
      : base(e => throw new UnificationError("Unhandled expression type: " + e.GetType()),
             UnwrapStmtExpr)
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

    // FIXME: move this function elsewhere
    public static bool ExpressionsEqual(Expression e1, Expression e2) {
      return new ExpressionEqualityVisitor(false).Visit(e1, e2);
    }

    internal void AddBinding(IVariable x, Expression e) {
      Expression val;
      if (map.TryGetValue(x, out val)) {
        if (!ExpressionsEqual(e, val)) {
          SimplifyingRewriter.DebugMsg($"Conflicting binding for {x.Name}" +
                                       $": {Printer.ExprToString(val)} & {Printer.ExprToString(e)}");
          throw new UnificationError("Conflicting binding for " + x + ": " + val + " & " + e);
        }
      } else {
        map.Add(x, e);
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
        // SimplifyingRewriter.DebugMsg($"Trying to add binding {e.Var.Name} |-> {Printer.ExprToString(target)}");
        AddBinding(e.Var, target);
        // SimplifyingRewriter.DebugMsg("Binding succeeded");
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
        var typeUnifier = new TypeUnifier(typeMap);
        typeUnifier.Visit(fc.TypeArgumentSubstitutions[key]
                          .NormalizeExpandKeepConstraints(),
                          fctarget.TypeArgumentSubstitutions[key]
                          .NormalizeExpandKeepConstraints());
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

    public object Visit(MemberSelectExpr e, Expression target) {
      Contract.Assert(e.Member != null);
      if (!(target is MemberSelectExpr)) {
        throw new UnificationError(e, target);
      }
      var t = (MemberSelectExpr)target;
      Visit(e.Obj.Resolved, t.Obj.Resolved);
      if (!e.Member.Equals(t.Member)) {
        throw new UnificationError(e, t);
      }
      // Should we use TypeArgumentSubstitutions here instead?
      if (e.TypeApplication.Count != t.TypeApplication.Count) {
        throw new UnificationError("Different number of type arguments: ", e, t);
      }
      for (int i = 0; i < e.TypeApplication.Count; i++) {
        TypeUnifier tu = new TypeUnifier(typeMap);
        tu.Visit(e.TypeApplication[i], t.TypeApplication[i]);
      }
      return null;
    }

    public override object Visit(ConcreteSyntaxExpression e, Expression target) {
      return Visit(e.Resolved, target.Resolved);
    }
  }

  public class SimplifyingRewriter : IRewriter {
    HashSet<Function> simplifierFuncs = new HashSet<Function>();
    HashSet<RewriteRule> simplifierRules = new HashSet<RewriteRule>();

    internal SimplifyingRewriter(ErrorReporter reporter) : base(reporter) {
      Contract.Requires(reporter != null);
    }

    internal void FindSimplificationCallables(ModuleDefinition m) {
      List<RewriteRule> defRules = new List<RewriteRule>();
      foreach (var decl in ModuleDefinition.AllCallables(m.TopLevelDecls)) {
        if (decl is Function) {
          Function f = (Function) decl;
          if (Attributes.Contains(f.Attributes, "simplifier")) {
            if (Attributes.Contains(f.Attributes, "simp")) {
              reporter.Error(MessageSource.Simplifier, f,
                             "Function cannot be both a simplifier and a simplification target");
            }
            if (f.Formals.Count != 1) {
              reporter.Error(MessageSource.Simplifier, f, "A simplifier function must take exactly one argument (and be an identity function)");
            }
            // TODO: Ensure that body is just the single formal parameter
            if (f.Body == null) {
              reporter.Error(MessageSource.Simplifier, f, "A simplifier function must have a body (and be an identity function)");
            }
            Contract.Assert(f.Body.Resolved != null);
            var ie = f.Body.Resolved as IdentifierExpr;
            if (ie == null || !ie.Var.Equals(f.Formals[0])) {
              reporter.Error(MessageSource.Simplifier, f, "A simplifier function must be an identity function");
            }
            simplifierFuncs.Add(f);
          }
        }
        else if (decl is Lemma) {
          Lemma l = (Lemma) decl;
          if (Attributes.Contains(l.Attributes, "simp")) {
            if (l.Ens.Count() == 1 &&
                l.Ens[0].E is BinaryExpr &&
                ((BinaryExpr)l.Ens[0].E).Op == BinaryExpr.Opcode.Eq) {
              var br = (BinaryExpr)l.Ens[0].E;
              simplifierRules.Add(new RewriteRule(br.E0, br.E1));
            } else {
              reporter.Error(MessageSource.Simplifier, l,
                             "A simplification lemma must have exactly one equality as ensures clause");
            }
          }
        }
      }
    }

    // FIXME: use Dafny's logging functions instead
    public static void DebugMsg(String s) {
      if (!DafnyOptions.O.SimpTrace) {
        return;
      }
      Console.WriteLine(s);
    }

    public static void DebugExpression(String prefix, Expression e, bool subexps=false) {
      if (!DafnyOptions.O.SimpTrace) {
        return;
      }
      Console.WriteLine(prefix + Printer.ExprToString(e) + "[" + e.GetType() + "]");
      if (subexps) {
        foreach (var subexp in e.SubExpressions) {
          DebugExpression("\t" + prefix, subexp.Resolved, subexps);
        }
      }
    }

    // Returns null iff unification failed.
    internal static UnificationVisitor UnifiesWith(Expression target, Expression pattern) {
      try {
        DebugExpression("Trying to unify: ", target);
        DebugExpression("with pattern: ", pattern);
        var uf = new UnificationVisitor();
        uf.Visit(pattern.Resolved, target);
        DebugMsg("Unification succeeded");
        return uf;
      } catch(UnificationError ue) {
        //DebugMsg($"Unification of {Printer.ExprToString(pattern)} and " +
        //         $"{Printer.ExprToString(target)} failed with:\n{ue}");
        return null;
      }
    }

    internal class SimplificationVisitor: ExpressionTransformer
    {
      HashSet<RewriteRule> simplifierLemmas;
      bool inGhost;

      internal static Expression WarnUnhandledCase(Expression e) {
        DebugMsg("[SimplificationVisitor] unhandled expression type: " +
                 $"{Printer.ExprToString(e)}[{e.GetType()}]");
        return e;
      }

      public SimplificationVisitor(HashSet<RewriteRule> simplifierLemmas, bool inGhost) :
        base(e => WarnUnhandledCase(e)) {
        this.simplifierLemmas = simplifierLemmas;
        this.inGhost = inGhost;
      }

      internal Expression CallDestructor(IToken tok, DatatypeDestructor dest, Expression val) {
        return new MemberSelectExpr(tok, val, dest);
      }
      // The wrapper parameter indicates what projection of the right-hand side we need
      // to use in the substitution; for example, when binding var (x, y) := e, we need
      // to replace x by e.0, but we no longer no that once we recurse into the CasePattern
      // representing (x, y).
      void BuildSubstMap(CasePattern<BoundVar> cp, Expression rhs,
                         Func<Expression, Expression> wrapper, SubstMap substMap,
                         IToken tok) {
        if (cp.Ctor is null) {
          // The binding is just to a normal variable instead of a pattern.
          Contract.Assert(cp.Var != null);
          substMap.Add(cp.Var, wrapper(rhs));
        } else {
          Contract.Assert(cp.Arguments.Count == cp.Ctor.Destructors.Count);
          for (int i = 0; i < cp.Arguments.Count; i++) {
            var arg = cp.Arguments[i];
            var dest = cp.Ctor.Destructors[i];
            Func<Expression, Expression> newWrapper = expr => CallDestructor(tok, dest, expr);
            BuildSubstMap(arg, rhs, expr => newWrapper(wrapper(expr)), substMap, tok);
          }
        }
      }
      internal Expression InlineLet(LetExpr e) {
        DebugExpression("Let expression: ", e);
        Contract.Assert(e.LHSs.Count == e.RHSs.Count);
        Dictionary<IVariable, Expression> substMap = new Dictionary<IVariable, Expression>();
        for (int i = 0; i < e.LHSs.Count; i++) {
          var lhs = e.LHSs[i];
          var rhs = e.RHSs[i];
          BuildSubstMap(lhs, rhs, expr => expr, substMap, e.tok);
        }
        // TODO: double-check receiverParam argument to Substitute
        var newBody = Translator.Substitute(e.Body, null, substMap);
        return newBody;
      }

      internal Option<Expression> RewriteBinaryExpr(BinaryExpr br) {
        // TODO: set/map/multiset literals are not LiteralExprs, so we need to handle these specially
        if (br.E0 is LiteralExpr && br.E1 is LiteralExpr &&
            br.E0.Type.Equals(br.E1.Type)) {
          List<BinaryExpr.ResolvedOpcode> eqOps =
            new List<BinaryExpr.ResolvedOpcode> {
            BinaryExpr.ResolvedOpcode.EqCommon,
            BinaryExpr.ResolvedOpcode.SeqEq,
            // BinaryExpr.ResolvedOpcode.SetEq,
            // BinaryExpr.ResolvedOpcode.MapEq,
            // BinaryExpr.ResolvedOpcode.MultiSetEq
          };
          List<BinaryExpr.ResolvedOpcode> neqOps =
            new List<BinaryExpr.ResolvedOpcode> {
            BinaryExpr.ResolvedOpcode.NeqCommon,
            BinaryExpr.ResolvedOpcode.SeqNeq,
          };
          var v1 = ((LiteralExpr)(br.E0)).Value;
          var v2 = ((LiteralExpr)(br.E1)).Value;
          if (eqOps.Contains(br.ResolvedOp)) {
            return new Some<Expression>(Expression.CreateBoolLiteral(br.tok, v1.Equals(v2)));
          } else if (neqOps.Contains(br.ResolvedOp)) {
            return new Some<Expression>(Expression.CreateBoolLiteral(br.tok, !v1.Equals(v2)));
          }
          if (v1 is BigInteger && v2 is BigInteger) {
            var i1 = (BigInteger)v1;
            var i2 = (BigInteger)v2;
            switch(br.ResolvedOp) {
              // Use braces around the cases so we can reuse newExpr as a variable name
              case BinaryExpr.ResolvedOpcode.Add: {
                // TODO: check if we need to do something special for negative numbers
                // like in Expression.CreateIntLiteral
                var newExpr = new LiteralExpr(br.tok, i1 + i2);
                newExpr.Type = br.Type;
                return new Some<Expression>(newExpr);
              }
              case BinaryExpr.ResolvedOpcode.Sub: {
                var newExpr = new LiteralExpr(br.tok, i1 - i2);
                newExpr.Type = br.Type;
                return new Some<Expression>(newExpr);
              }
              case BinaryExpr.ResolvedOpcode.Mul: {
                var newExpr = new LiteralExpr(br.tok, i1 * i2);
                newExpr.Type = br.Type;
                return new Some<Expression>(newExpr);
              }
              case BinaryExpr.ResolvedOpcode.Div: {
                var newExpr = new LiteralExpr(br.tok, i1 / i2);
                newExpr.Type = br.Type;
                return new Some<Expression>(newExpr);
              }
              case BinaryExpr.ResolvedOpcode.Le:
                return new Some<Expression>(Expression.CreateBoolLiteral(br.tok, i1 <= i2));
              case BinaryExpr.ResolvedOpcode.Lt:
                return new Some<Expression>(Expression.CreateBoolLiteral(br.tok, i1 < i2));
              case BinaryExpr.ResolvedOpcode.Gt:
                return new Some<Expression>(Expression.CreateBoolLiteral(br.tok, i1 > i2));
              case BinaryExpr.ResolvedOpcode.Ge:
                return new Some<Expression>(Expression.CreateBoolLiteral(br.tok, i1 >= i2));
            }
          }
        }
        return new None<Expression>();
      }


      public override Option<Expression> VisitOneExpr(Expression e, object st) {
        // TODO: make inlining lets configurable once we support different
        // sets of simplification rules (then one can add a special simplification set)
        // containing just this rule that users can request where needed
        if (e is LetExpr && inGhost) {
          DebugExpression("Inlining LetExpr: ", e);
          var newE = InlineLet((LetExpr)e);
          if (newE != e) {
            DebugExpression("Inlined result: ", newE);
            return new Some<Expression>(newE);
          }
        }
        // try to rewrite comparisons between literals
        if (e is BinaryExpr) {
          var rewritten = RewriteBinaryExpr((BinaryExpr)e);
          if (rewritten is Some<Expression>) {
            return rewritten;
          }
        }
        // Rewrite constructor fields
        if (e is MemberSelectExpr) {
          var ms = (MemberSelectExpr) e;
          if (ms.Obj is DatatypeValue) {
            var obj = (DatatypeValue)ms.Obj;
            // Check if member we selected is the query field of one of the
            // constructors:
            foreach (var ctor in obj.Ctor.EnclosingDatatype.Ctors) {
              if (ctor.QueryField.Equals(ms.Member)) {
                var newExpr = Expression.CreateBoolLiteral(ms.tok, ctor.Equals(obj.Ctor));
                return new Some<Expression>(newExpr);
              }
            }
            // Check if we are projecting to a concrete field of the constructor
            // This is also implementable from within dafny by adding a lemma
            // for each field of each constructor, but we don't want the user
            // to have to write all that boilerplate.
            Contract.Assert(obj.Ctor.Destructors.Count == obj.Arguments.Count);
            for (int i = 0; i < obj.Ctor.Destructors.Count; i++) {
              var dtor = obj.Ctor.Destructors[i];
              if (dtor.Equals(ms.Member)) {
                return new Some<Expression>(obj.Arguments[i]);
              }
            }
          }
        }
        // inline function calls to functions that have simp attribute
        if (e is FunctionCallExpr) {
          var fc = (FunctionCallExpr)e;
          // TODO: make "simp" a constant
          if (Attributes.Contains(fc.Function.Attributes, "simp")) {
            Dictionary<IVariable, Expression> substMap = new Dictionary<IVariable, Expression>();
            Contract.Assert(fc.Args.Count == fc.Function.Formals.Count);
            for (int i = 0; i < fc.Args.Count; i++) {
              substMap.Add(fc.Function.Formals[i], fc.Args[i]);
            }
            var substitutedBody = Translator.Substitute(fc.Function.Body, null, substMap,
                                                        fc.TypeArgumentSubstitutions);
            return new Some<Expression>(substitutedBody);
          }
        }
        foreach (var simpLem in simplifierLemmas) {
          var uv = UnifiesWith(e.Resolved, simpLem.Lhs);
          if (uv != null) {
            // DebugMsg(e.Resolved + " unifies with " + eq.E0.Resolved);
            // FIXME: check that we don't need the receiverParam argument
            var res = Translator.Substitute(simpLem.Rhs, null, uv.GetSubstMap, uv.GetTypeSubstMap);
            return new Some<Expression>(res);
          }
        }
        return new None<Expression>();
      }

    }


    internal class SimplifyInExprVisitor : ExpressionTransformer
    {
      ErrorReporter reporter;
      HashSet<Function> simplifierFuncs;
      HashSet<RewriteRule> simplifierRules;
      bool inGhost;

      internal static Expression WarnUnhandledCase(Expression e) {
        DebugMsg("[SimplifyInExprVisitor] unhandled expression type" +
                 $"{Printer.ExprToString(e)}[{e.GetType()}]");
        return e;
      }

      public SimplifyInExprVisitor(ErrorReporter reporter,
                                   HashSet<Function> simplifierFuncs,
                                   HashSet<RewriteRule> simplifierRules,
                                   bool inGhost) :
        base(e => WarnUnhandledCase(e)) {
        this.reporter = reporter;
        this.simplifierFuncs = simplifierFuncs;
        this.simplifierRules = simplifierRules;
        this.inGhost = inGhost;
      }

      internal Expression Simplify(Expression e) {
        var expr = e;
        // Keep trying to simplify until we (hopefully) reach a fixpoint
        // FIXME: add parameter to control maximum simplification steps?
        DebugExpression("Simplifying expression: ", e);
        while(true) {
          var sv = new SimplificationVisitor(simplifierRules, inGhost);
          var simplified = sv.Visit(expr, null);
          if (simplified == expr) {
            break;
          } else {
            expr = simplified;
          }
        }
        DebugExpression("Simplification result: ", expr, true);
        reporter.Info(MessageSource.Simplifier, e.tok, $"Simplified to {Printer.ExprToString(expr)}");
        return expr;
      }

      public override Expression Visit(FunctionCallExpr fc, object st) {
        DebugExpression($"Visiting function call to {fc.Function.Name}", fc);
        if (IsSimplifierCall(fc)) {
          DebugMsg("Found call to simplifier: " + Printer.ExprToString(fc));
          Contract.Assert(fc.Args.Count == 1);
          var res  = Simplify(fc.Args[0]);
          return res;
        } else {
          return fc;
        }
      }

      public override Option<Expression> VisitOneExpr(Expression e, object st) {
        DebugExpression("SimplifyInExprVisitor called: ", e);
        return new None<Expression>();
      }
    }

    protected Expression SimplifyInExpr(Expression e, bool inGhost) {
      var sv = new SimplifyInExprVisitor(reporter, simplifierFuncs, simplifierRules, inGhost);
      return sv.Visit(e, null);
    }

    internal Statement SimplifyInStmt(Statement stmt, bool inGhost) {
      var exprVis = new SimplifyInExprVisitor(reporter, simplifierFuncs, simplifierRules, inGhost);
      var stmtSimplifyVis = new StatementTransformer(exprVis);
      return stmtSimplifyVis.Visit(stmt, null);
    }

    internal void SimplifyCalls(ModuleDefinition m) {
      foreach (var callable in ModuleDefinition.AllCallables(m.TopLevelDecls)) {
        if (callable is Function) {
          Function fun = (Function) callable;
          if (fun.Body is ConcreteSyntaxExpression) {
            ((ConcreteSyntaxExpression)fun.Body).ResolvedExpression =
              SimplifyInExpr(fun.Body.Resolved, fun.IsGhost);
          }
        } else if (callable is Method) {
          Method meth = (Method) callable;
          if (meth.Body != null) {
            var newBody = SimplifyInStmt(meth.Body, meth.IsGhost);
            Contract.Assert(newBody is BlockStmt);
            meth.Body = (BlockStmt)newBody;
            DebugMsg($"New body for {meth.Name}: {Printer.StatementToString(meth.Body)}");
          }
        }
      }
    }

    internal override void PostResolve(ModuleDefinition m) {
      FindSimplificationCallables(m);
      SimplifyCalls(m);
    }
  }

  internal class RewriteRule {
    public readonly Expression Lhs;
    public readonly Expression Rhs;
    public RewriteRule(Expression lhs, Expression rhs) {
      this.Lhs = lhs;
      this.Rhs = rhs;
    }
  }
}
