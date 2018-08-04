using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using System.Reflection;
using System.Text;
using System.Diagnostics;
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

    // This is a bit of an ad-hoc extension to handle StmtExprs in the
    // unification visitor to avoid having to call this function on each
    // recursive call.
    internal Func<S, S> transformState;

    public ExpressionVisitor(Func<S, S> transformState=null) {
      if (transformState == null) {
        this.transformState = (s) => s;
      } else {
        this.transformState = transformState;
      }
    }

    public virtual R VisitDefault(Expression e, S st) {
      return default(R);
    }

    public virtual R Visit(Expression e, S st) {
      Option<R> res = VisitOneExpr(e, transformState(st));
      if (res is Some<R>) {
        return ((Some<R>)res).val;
      }
      if (e is ConcreteSyntaxExpression) {
        if (((ConcreteSyntaxExpression)e).ResolvedExpression == null) {
          return VisitDefault(e, st);
        }
        return Visit(e.Resolved, transformState(st));
      }
      /*
      if (e is StringLiteralExpr) {
        return Visit((StringLiteralExpr)e, st);
      } else if (e is LiteralExpr) {
        return Visit((LiteralExpr)e, st);
      } */
      // A hacky way to do double dispatch without enumerating all the subclasses
      // of Expression:
      //PerfTimers.StartTimer("Reflection");
      /*
      var method = from m in GetType().GetMethods()
        where m.Name == "Visit"
        && m.GetParameters().Length==2
        && e.GetType().IsAssignableFrom(m.GetParameters()[0].ParameterType)
        && typeof(S).IsAssignableFrom(m.GetParameters()[1].ParameterType)
        && m.ReturnType == typeof(R)
        select m;
      var methods = method.ToList();
      */
      PerfTimers.StartTimer("DynamicDispatch");
      if (e is StringLiteralExpr) {
        PerfTimers.StopTimer("DynamicDispatch");
        return Visit((StringLiteralExpr)e, st);
      } else if (e is BinaryExpr) {
        PerfTimers.StopTimer("DynamicDispatch");
        return Visit((BinaryExpr)e, st);
      } else if (e is LiteralExpr) {
        PerfTimers.StopTimer("DynamicDispatch");
        return Visit((LiteralExpr)e, st);
      } else if (e is UnaryOpExpr) {
        PerfTimers.StopTimer("DynamicDispatch");
        return Visit((UnaryOpExpr)e, st);
      } else if (e is FunctionCallExpr) {
        PerfTimers.StopTimer("DynamicDispatch");
        return Visit((FunctionCallExpr)e, st);
      } else if (e is LetExpr) {
        PerfTimers.StopTimer("DynamicDispatch");
        return Visit((LetExpr)e, st);
      } else if (e is StmtExpr) {
        PerfTimers.StopTimer("DynamicDispatch");
        return Visit((StmtExpr)e, st);
      } else if (e is IdentifierExpr) {
        PerfTimers.StopTimer("DynamicDispatch");
        return Visit((IdentifierExpr)e, st);
      } else if (e is TernaryExpr) {
        PerfTimers.StopTimer("DynamicDispatch");
        return Visit((TernaryExpr)e, st);
      } else if (e is ITEExpr) {
        PerfTimers.StopTimer("DynamicDispatch");
        return Visit((ITEExpr)e, st);
      } else if (e is DatatypeValue) {
        PerfTimers.StopTimer("DynamicDispatch");
        return Visit((DatatypeValue)e, st);
      } else if (e is MemberSelectExpr) {
        PerfTimers.StopTimer("DynamicDispatch");
        return Visit((MemberSelectExpr)e, st);
      } else {
        PerfTimers.StopTimer("DynamicDispatch");
        Contract.Assert(false, $"Unhandled expression type {Printer.ExprToString(e)}" +
                        $" [{e.GetType()}]");
        return VisitDefault(e, st);
      }
      /*
      if (methods.Count() == 0) {
        // Console.WriteLine("No suitable method for expression of type: " + e.GetType());
        return this.defaultRet(e);
      } if (methods.Count() > 1) {
        throw new System.ArgumentException("More than one visit method for: " + e.GetType());
      } else {
        try {
          return (R) methods[0].Invoke(this, new object[]{e, transformState(st)});
        } catch(TargetInvocationException tie) {
          if (tie.InnerException is UnificationError) {
            throw tie.InnerException;
          }
          throw tie;
        }
      } */
    }

    public virtual R Visit(ConcreteSyntaxExpression e, S st) {
      // For the purposes of the simplifier we only want to operate
      // on resolved expressions.
      return Visit(e.ResolvedExpression, st);
    }

    public virtual Option<R> VisitOneExpr(Expression e, S st) {
      return new None<R>();
    }

    public virtual R Visit(StringLiteralExpr e, S st) {
      return VisitDefault(e, st);
    }

    public virtual R Visit(BinaryExpr e, S st) {
      return VisitDefault(e, st);
    }

    public virtual R Visit(LiteralExpr e, S st) {
      return VisitDefault(e, st);
    }

    public virtual R Visit(UnaryOpExpr e, S st) {
      return VisitDefault(e, st);
    }

    public virtual R Visit(FunctionCallExpr e, S st) {
      return VisitDefault(e, st);
    }

    public virtual R Visit(LetExpr e, S st) {
      return VisitDefault(e, st);
    }

    public virtual R Visit(StmtExpr e, S st) {
      return VisitDefault(e, st);
    }

    public virtual R Visit(IdentifierExpr e, S st) {
      return VisitDefault(e, st);
    }

    public virtual R Visit(TernaryExpr e, S st) {
      return VisitDefault(e, st);
    }

    public virtual R Visit(ITEExpr e, S st) {
      return VisitDefault(e, st);
    }

    public virtual R Visit(DatatypeValue e, S st) {
      return VisitDefault(e, st);
    }

    public virtual R Visit(MemberSelectExpr e, S st) {
      return VisitDefault(e, st);
    }

  }

  // A visitor for transforming expressions. Since expression fields are
  // readonly, we need to rebuild an expression as soon as we want to change any
  // part of it.
  public class ExpressionTransformer: ExpressionVisitor<Expression, object>
  {
    public ExpressionTransformer()
    {
    }

    public override Expression VisitDefault(Expression e, object st) {
      return e;
    }

    public override Expression Visit(BinaryExpr e, object st) {
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

    public override Expression Visit(UnaryOpExpr e, object st) {
      var eNew = Visit(e.E, st);
      if (e != eNew) {
        var res = new UnaryOpExpr(e.tok, e.Op, eNew);
        res.Type = e.Type;
        return res;
      }
      return e;
    }

    public override Expression Visit(TernaryExpr e, object st) {
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

    public override Expression Visit(ITEExpr e, object st) {
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

    public override Expression Visit(FunctionCallExpr e, object st) {
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

    public override Expression Visit(IdentifierExpr e, object st) {
      return e;
    }

    public override Expression Visit(DatatypeValue dv, object st) {
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

    public override Expression Visit(MemberSelectExpr e, object st) {
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

    public override Expression Visit(StmtExpr e, object st) {
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

    /* public virtual Expression Visit(StringLiteralExpr e, object st) {
      return e;
    } */

    public override Expression Visit(LiteralExpr e, object st) {
      return e;
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
      // SimplifyingRewriter.DebugExpression("StatementTransformer: visiting expression: ", e);
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
      // SimplifyingRewriter.DebugMsg($"Visiting statement {Printer.StatementToString(s)}");
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
    bool def;
    public ExpressionEqualityVisitor(bool def) {
      this.def = def;
    }

    public override bool VisitDefault(Expression e, Expression rhs) {
      return def;
    }

    public override bool Visit(LiteralExpr e, Expression rhs) {
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

    public void Reset() {
      map = new Dictionary<IVariable, Expression>();
      typeMap = new Dictionary<TypeParameter, Type>();
    }

    public UnificationVisitor()
      : base(UnwrapStmtExpr)
    {
      this.boundVars = new Stack<HashSet<IVariable>>();
    }

    public override object VisitDefault(Expression e, Expression target) {
      throw new UnificationError("Unhandled expression type: " + e.GetType());
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

    public override object Visit(TernaryExpr e, Expression target) {
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

    public override object Visit(IdentifierExpr e, Expression target) {
      if (e.DontUnify) {
        var iet = target as IdentifierExpr;
        // in this case, the LHS might not be resolved, so we need to
        // syntactically check the name; I'm not sure if there's a better option here.
        if (iet == null || !iet.Name.Equals(e.Name)) {
          throw new UnificationError(e, target);
        }
        return null;
      }
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

    public override object Visit(ITEExpr e, Expression target) {
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

    public override object Visit(FunctionCallExpr fc, Expression target) {
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


    public override object Visit(BinaryExpr be, Expression target) {
      if (!(target is BinaryExpr)) {
        throw new UnificationError(be, target);
      }
      var btarget = (BinaryExpr)target;
      if (!btarget.ResolvedOp.Equals(be.ResolvedOp)) {
        throw new UnificationError(be, target);
      }
      Visit(be.E0, btarget.E0);
      Visit(be.E1, btarget.E1);
      return null;
    }

    public override object Visit(LiteralExpr le, Expression target) {
      if (!(target is LiteralExpr)) {
        throw new UnificationError(le, target);
      }
      if (!le.Value.Equals(((LiteralExpr)target).Value)) {
        throw new UnificationError(le, target);
      }
      return null;
    }

    public override object Visit(UnaryOpExpr ue, Expression target) {
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

    public override object Visit(DatatypeValue dv, Expression target) {
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

    public override object Visit(MemberSelectExpr e, Expression target) {
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
    RuleSet simplifierRules = new RuleSet();
    public static SimplifyingRewriter S;
    public static Dictionary<Expression, Expression> Simplifications =
      new Dictionary<Expression, Expression>();
    public static ErrorReporter errReporter;

    internal SimplifyingRewriter(ErrorReporter reporter) : base(reporter) {
      Contract.Requires(reporter != null);
      SimplifyingRewriter.errReporter = reporter;
      S = this;
    }

    internal void FindSimplificationCallables(ModuleDefinition m) {
      RuleSet defRules = new RuleSet();
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
              simplifierRules.AddRule(new RewriteRule(br.E0, br.E1));
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
      Contract.Assert(e != null);
      Console.WriteLine(prefix + Printer.ExprToString(e) + "[" + e.GetType() + "]");
      if (subexps) {
        foreach (var subexp in e.SubExpressions) {
          DebugExpression("\t" + prefix, subexp.Resolved, subexps);
        }
      }
    }

    internal class RewriteVisitor: ExpressionTransformer
    {
      RuleSet simplifierLemmas;
      RuleSet localRules;
      bool inGhost;
      int subtermNo = 0;
      bool anyChange;
      UnificationVisitor uv;

      public override Expression VisitDefault(Expression e, object st) {
        // DebugMsg("[SimplificationVisitor] unhandled expression type: " +
        //          $"{Printer.ExprToString(e)}[{e.GetType()}]");
        return e;
      }

      public RewriteVisitor(RuleSet simplifierLemmas, RuleSet localRules, bool inGhost)
      {
        this.simplifierLemmas = simplifierLemmas;
        this.localRules = localRules;
        this.inGhost = inGhost;
        this.anyChange = false;
        uv = new UnificationVisitor();
      }

      public void Reset() { anyChange = false; }

      public bool AnyChange {
        get {
          return anyChange;
        }
      }

      public enum Mode {
        NORMALIZE, REWRITE, UNFOLD
      }

      public Mode RewriteMode;

      internal Expression UnfoldFunction(FunctionCallExpr fc) {
        PerfTimers.StartTimer("InlineFunction");
        Dictionary<IVariable, Expression> substMap = new Dictionary<IVariable, Expression>();
        Contract.Assert(fc.Args.Count == fc.Function.Formals.Count);
        for (int i = 0; i < fc.Args.Count; i++) {
          substMap.Add(fc.Function.Formals[i], fc.Args[i]);
        }
        var substitutedBody = Translator.Substitute(fc.Function.Body, null, substMap,
                                                    fc.TypeArgumentSubstitutions);
        PerfTimers.RuleUse("inline");
        PerfTimers.StopTimer("InlineFunction");
        // DebugMsg($"Unfolding function {fc.Function.Name} to {Printer.ExprToString(substitutedBody)}");
        return substitutedBody;
      }

      internal Option<Expression> Unfold(Expression e, object st) {
        if (e is FunctionCallExpr) {
          var fc = (FunctionCallExpr)e;
          // TODO: make "simp" a constant
          if (Attributes.Contains(fc.Function.Attributes, "simp")) {
            anyChange = true;
            return new Some<Expression>(UnfoldFunction(fc));
          }
        }
        return new None<Expression>();
      }


      public Expression FullyNormalize(Expression e) {
        var expr = e;
        var oldMode = RewriteMode;
        RewriteMode = Mode.NORMALIZE;
        while (true) {
          Reset();
          var newExpr = Visit(expr, null);
          if (!AnyChange) {
            break;
          }
          expr = newExpr;
        }
        RewriteMode = oldMode;
        return expr;
      }

      public override Option<Expression> VisitOneExpr(Expression e, object st) {
        // TODO: make inlining lets configurable once we support different
        // sets of simplification rules (then one can add a special simplification set)
        // containing just this rule that users can request where needed
        Option<Expression> res = null;
        switch (RewriteMode) {
          case Mode.NORMALIZE:
            PerfTimers.StartTimer("Normalize");
            res = Normalize(e, st);
            PerfTimers.StopTimer("Normalize");
            break;
          case Mode.REWRITE:
            PerfTimers.StartTimer("Rewrite");
            res = Rewrite(e, st);
            PerfTimers.StopTimer("Rewrite");
            break;
          case Mode.UNFOLD:
            PerfTimers.StartTimer("Unfold");
            res = Unfold(e, st);
            PerfTimers.StopTimer("Unfold");
            break;
        }
        if (res is Some<Expression>) {
          //DebugMsg($"Rewriting[{RewriteMode}]..");
          anyChange = true;
          var resExpr = (res as Some<Expression>).val;
          // return new Some<Expression>(Visit(resExpr, st));
        }
        return res;
      }

      internal bool UnifiesWith(Expression target, Expression pattern) {
        try {
          if (pattern.WasResolved()) {
            pattern = pattern.Resolved;
          }
          // DebugExpression("Trying to unify: ", target);
          // DebugExpression("with pattern: ", pattern);
          // Fail early without a lot of dynamic type checks

          //if (pattern is FunctionCallExpr || pattern is DatatypeValue){
          //  if (pattern.Tag == null)  {
          //    DebugMsg("Found untagged expression");
          //  } else {
          //    DebugMsg("Found tagged expression");
          //  }
          //}
          if (target.Tag != null && pattern.Tag != null &&
              target.Tag != pattern.Tag) {
            // DebugMsg($"Skipping unification since tags don't match: {((ExpressionTag)(target.Tag)).Name()} & {((ExpressionTag)(pattern.Tag)).Name()}");
            return false;
          }
          uv.Reset();
          uv.Visit(pattern, target);
          // DebugMsg("Unification succeeded");
          //if (DafnyOptions.O.SimpTrace) {
          //  foreach (var item in uv.GetSubstMap) {
          //    //DebugMsg($"\t{item.Key} |-> {Printer.ExprToString(item.Value)}");
          //  }
          //}
          return true;
        } catch(UnificationError ue) {
          //DebugMsg($"Unification of {Printer.ExprToString(pattern)} and " +
          //         $"{Printer.ExprToString(target)} failed with:\n{ue}");
          return false;
        }
      }

      internal Option<Expression> TrySimplify(Expression e, RewriteRule rr) {
        // Stopwatch s = new Stopwatch();
        PerfTimers.Timers[PerfTimers.UNIFICATION].Start();
        var unifies = UnifiesWith(e.Resolved, rr.Lhs);
        PerfTimers.UnificationAttempts++;
        PerfTimers.Timers[PerfTimers.UNIFICATION].Stop();
        if (unifies) {
          PerfTimers.Timers[PerfTimers.FIND_RULE].Stop();
          // DebugMsg(e.Resolved + " unifies with " + eq.E0.Resolved);
          // FIXME: check that we don't need the receiverParam argument
          PerfTimers.StartTimer("Substitute");
          var res = Translator.Substitute(rr.Rhs, null, uv.GetSubstMap, uv.GetTypeSubstMap);
          PerfTimers.StopTimer("Substitute");
          return new Some<Expression>(res);
        }
        return new None<Expression>();
      }

      public Option<Expression> Rewrite(Expression e, object st) {
        subtermNo++;
        Action<object> subtermFound = (o => {
            PerfTimers.MatchingSubtermNos.Add(subtermNo);
            DebugMsg($"Successful rewrite in subterm {subtermNo}");
            subtermNo = 0;
          });
        Stopwatch s = new Stopwatch();
        s.Start();
        int ruleNo = 0;
        PerfTimers.Timers[PerfTimers.FIND_RULE].Start();
        foreach (var simpLem in localRules.Rules()) {
          ruleNo++;
          PerfTimers.TriedRules++;
          var simped = TrySimplify(e, simpLem) as Some<Expression>;
          if (simped != null) {
            s.Stop();
            var t = s.ElapsedMilliseconds;
            PerfTimers.RuleAttempts.Add(ruleNo);
            DebugMsg($"Found matching rule on {ruleNo}th try after {((double)(s.ElapsedMilliseconds))/1000}s");
            PerfTimers.RuleFindingTimes.Add(t);
            subtermFound(null);
            PerfTimers.RuleUse("local");
            return simped;
          }
        }
        PerfTimers.Timers[PerfTimers.FIND_RULE].Start();
        // As a heuristic we sort the simplifier lemmas by "similarity" to the
        // expression we are looking at; we use number of shared constructor and
        // function applications as a proxy for likelihood to match this.
        foreach (var simpLem in simplifierLemmas.RulesFor(e)) {
          ruleNo++;
          PerfTimers.TriedRules++;
          var simped = TrySimplify(e, simpLem) as Some<Expression>;
          if (simped != null) {
            s.Stop();
            var t = s.ElapsedMilliseconds;
            PerfTimers.RuleAttempts.Add(ruleNo);
            DebugMsg($"Found matching rule on {ruleNo}th try after {((double)(s.ElapsedMilliseconds))/1000}s");
            PerfTimers.RuleFindingTimes.Add(t);
            subtermFound(null);
            PerfTimers.RuleUse("global");
            return simped;
          }
        }
        return Unfold(e, st);
        // PerfTimers.Timers[PerfTimers.FIND_RULE].Stop();
        // // inline function calls to functions that have simp attribute
        // return new None<Expression>();
      }

      public Option<Expression> Normalize(Expression e, object st) {
        var ite = e as ITEExpr;
        if (e is LetExpr && inGhost) {
          // DebugExpression("Inlining LetExpr: ", e);
          PerfTimers.StartTimer(PerfTimers.LET_INLINING);
          var newE = InlineLet((LetExpr)e);
          PerfTimers.StopTimer(PerfTimers.LET_INLINING);
          if (newE != e) {
            // DebugExpression("Inlined result: ", newE);
            PerfTimers.RuleUse("let");
            return new Some<Expression>(newE);
          }
        } else if (e is BinaryExpr) {
          // try to rewrite comparisons between literals
          PerfTimers.StartTimer("RewriteBinaryExpr");
          var rewritten = RewriteBinaryExpr((BinaryExpr)e);
          PerfTimers.StopTimer("RewriteBinaryExpr");
          if (rewritten is Some<Expression>) {
            PerfTimers.RuleUse("RewriteBinaryExpr");
            return rewritten;
          }
        } else if (e is UnaryOpExpr) {
          var uo = (UnaryOpExpr)e;
          if (uo.E is LiteralExpr) {
            var v1 = ((LiteralExpr)uo.E).Value;
            if ((v1 is bool) && uo.Op == UnaryOpExpr.Opcode.Not) {
              return new Some<Expression>(Expression.CreateBoolLiteral(uo.tok, !((bool)v1)));
            }
          }
        } else if (ite != null && ite.Test is LiteralExpr) {
          var guard = ite.Test as LiteralExpr;
          if ((bool)guard.Value) {
            return new Some<Expression>(ite.Thn);
          } else {
            return new Some<Expression>(ite.Els);
          }
          // ifs with literal booleans as guards
        } else if (e is MemberSelectExpr) {
          // Rewrite constructor fields
          PerfTimers.StartTimer("MemberSelectExpr");
          var ms = (MemberSelectExpr) e;
          if (ms.Obj.Resolved is DatatypeValue) {
            var obj = (DatatypeValue)ms.Obj.Resolved;
            // Check if member we selected is the query field of one of the
            // constructors:
            foreach (var ctor in obj.Ctor.EnclosingDatatype.Ctors) {
              if (ctor.QueryField.Equals(ms.Member)) {
                var newExpr = Expression.CreateBoolLiteral(ms.tok, ctor.Equals(obj.Ctor));
                PerfTimers.RuleUse("ctor?");
                PerfTimers.StopTimer("MemberSelectExpr");
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
                PerfTimers.RuleUse("dtor");
                PerfTimers.StopTimer("MemberSelectExpr");
                return new Some<Expression>(obj.Arguments[i]);
              }
            }
          }
          PerfTimers.StopTimer("MemberSelectExpr");
        }
        return new None<Expression>();
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
        // DebugExpression("Let expression: ", e);
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
        if (br.ResolvedOp == BinaryExpr.ResolvedOpcode.And ||
            br.ResolvedOp == BinaryExpr.ResolvedOpcode.Or) {
          var l1 = br.E0 as LiteralExpr;
          var l2 = br.E1 as LiteralExpr;
          if (l1 != null) {
            var b1 = (bool)l1.Value;
            if (br.ResolvedOp == BinaryExpr.ResolvedOpcode.And) {
              if (b1) {
                return new Some<Expression>(br.E1);
              } else {
                return new Some<Expression>(Expression.CreateBoolLiteral(br.tok, false));
              }
            } else {
              if (b1) {
                return new Some<Expression>(Expression.CreateBoolLiteral(br.tok, true));
              } else {
                return new Some<Expression>(br.E1);
              }
            }
          } else if (l2 != null) {
            var b2 = (bool)l2.Value;
            if (br.ResolvedOp == BinaryExpr.ResolvedOpcode.And) {
              if (b2) {
                return new Some<Expression>(br.E0);
              } else {
                return new Some<Expression>(Expression.CreateBoolLiteral(br.tok, false));
              }
            } else {
              if (b2) {
                return new Some<Expression>(Expression.CreateBoolLiteral(br.tok, true));
              } else {
                return new Some<Expression>(br.E0);
              }
            }
          } else {
            return new None<Expression>();
          }
        }
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

      public Expression FullySimplify(Expression e, object st) {
        var expr = e;
        var oldMode = RewriteMode;
        while (true) {
          Reset();
          RewriteMode = Mode.NORMALIZE;
          var normalized = Visit(expr, st);
          if (AnyChange) {
            expr = normalized;
            continue;
          }
          Reset();
          RewriteMode = Mode.REWRITE;
          expr = Visit(normalized, st);
          if (!AnyChange) {
            break;
          }
        }
        return expr;
      }

    }

    internal class SimplificationVisitor : ExpressionTransformer
    {
      RuleSet simplifierRules;
      RuleSet localRules;
      bool inGhost;
      Func<Expression, Expression> defRet;
      RewriteVisitor rv;
      public bool Matched;

      public RewriteVisitor Rewriter {
        get {
          return rv;
        }
      }

      public override Expression VisitDefault(Expression e, object st) {
        return rv.FullySimplify(e, st);
      }
      public SimplificationVisitor(RuleSet simplifierRules, RuleSet localRules, bool inGhost)
      {
        this.simplifierRules = simplifierRules;
        this.localRules = localRules;
        this.inGhost = inGhost;
        rv = new RewriteVisitor(simplifierRules, localRules, inGhost);
      }

      public override Expression Visit(ITEExpr e, object st) {
        Matched = true;
        var newTest = rv.FullySimplify(e.Test, st);
        var litTest = newTest as LiteralExpr;
        if (litTest != null && (litTest.Value is bool)) {
          if ((bool)litTest.Value) {
            return Visit(e.Thn, st);
          } else {
            return Visit(e.Els, st);
          }
        } else {
          return rv.FullySimplify(e, null);
        }
      }
    }


    internal class SimplifyInExprVisitor : ExpressionTransformer
    {
      ErrorReporter reporter;
      HashSet<Function> simplifierFuncs;
      RuleSet simplifierRules;
      RuleSet localRewriteRules;
      bool inGhost;

      // Remove all local rewrite rules where v occurs on right-hand side
      public void VariableChanged(IVariable v) {
        List<RewriteRule> invalidRules = new List<RewriteRule>();
        foreach (var lrule in localRewriteRules.Rules()) {
          var fvs = Translator.ComputeFreeVariables(lrule.Rhs);
          if (fvs.Contains(v)) {
            invalidRules.Add(lrule);
          }
        }
        foreach (var irule in invalidRules) {
          localRewriteRules.RemoveRule(irule);
        }
      }

      public void AddLocalRewriteRule(RewriteRule rr) {
        localRewriteRules.AddRule(rr);
      }

      public override Expression VisitDefault(Expression e, object st) {
        // DebugMsg("[SimplifyInExprVisitor] unhandled expression type" +
        //          $"{Printer.ExprToString(e)}[{e.GetType()}]");
        return e;
      }

      public SimplifyInExprVisitor(ErrorReporter reporter,
                                   HashSet<Function> simplifierFuncs,
                                   RuleSet simplifierRules,
                                   bool inGhost)
      {
        this.reporter = reporter;
        this.simplifierFuncs = simplifierFuncs;
        this.simplifierRules = simplifierRules;
        this.inGhost = inGhost;
        this.localRewriteRules = new RuleSet();
      }

      internal Expression Simplify(Expression e) {
        Expression result;
        if (SimplifyingRewriter.Simplifications.TryGetValue(e, out result)) {
          DebugMsg("using memoized result");
          return result;
        }
        /*
          var sv = new SimplificationVisitor(simplifierRules, localRewriteRules, inGhost);
          sv.Matched = false;
          result = sv.Visit(e, null);
          if (!sv.Matched) {
          result = sv.Rewriter.FullySimplify(e, null);
          }
          var msg = $"Simplified to {Printer.ExprToString(result)}";
          DebugMsg(msg);
          if (DafnyOptions.O.SimpTrace) {
          reporter.Warning(MessageSource.Simplifier, e.tok, msg);
          } else {
          reporter.Info(MessageSource.Simplifier, e.tok, msg);
          }
          SimplifyingRewriter.Simplifications[e] = result;
          return result; */
        var expr = e;
        // Keep trying to simplify until we (hopefully) reach a fixpoint
        // FIXME: add parameter to control maximum simplification steps?
        var exprStr = Printer.ExprToString(expr);
        if (exprStr.Count() >= 100) {
          exprStr = exprStr.Substring(0, 100);
        }
        DebugMsg($"Simplifying expression: {exprStr}...");
        var rewriter = new RewriteVisitor(simplifierRules, localRewriteRules, inGhost);
        var tagger = new ExpressionTagger();
        while(true) {
          PerfTimers.StartTimer("Tag");
          tagger.Visit(expr, null);
          PerfTimers.StopTimer("Tag");
          exprStr = Printer.ExprToString(expr);
          if (exprStr.Count() >= 100) {
            exprStr = exprStr.Substring(0, 100);
          }
          DebugMsg($"Simplifying expression: {exprStr}...");
          rewriter.Reset();
          expr = rewriter.FullyNormalize(expr);
          // DebugMsg("Done normalizing");
          PerfTimers.StartTimer("Tag");
          tagger.Visit(expr, null);
          PerfTimers.StopTimer("Tag");
          rewriter.RewriteMode = RewriteVisitor.Mode.REWRITE;
          var exprNew = rewriter.Visit(expr, null);
          if (!rewriter.AnyChange || expr == exprNew) {
            break;
          }
          expr = exprNew;
        }
        var msg = $"Simplified to {Printer.ExprToString(expr)}";
        DebugMsg(msg);
        if (DafnyOptions.O.SimpTrace) {
          reporter.Warning(MessageSource.Simplifier, e.tok, msg);
        } else {
          reporter.Info(MessageSource.Simplifier, e.tok, msg);
        }
        SimplifyingRewriter.Simplifications[e] = expr;
        return expr;
      }

      public bool IsSimplifierCall(FunctionCallExpr fc) {
        return simplifierFuncs.Contains(fc.Function);
      }

      public override Expression Visit(FunctionCallExpr fc, object st) {
        // DebugExpression($"Visiting function call to {fc.Function.Name}", fc);
        if (IsSimplifierCall(fc)) {
          // DebugMsg("Found call to simplifier: " + Printer.ExprToString(fc));
          Contract.Assert(fc.Args.Count == 1);
          var res  = Simplify(fc.Args[0]);
          return res;
        } else {
          return fc;
        }
      }

      public override Option<Expression> VisitOneExpr(Expression e, object st) {
        // DebugExpression("SimplifyInExprVisitor called: ", e);
        return new None<Expression>();
      }
    }

    internal class SimplifyInStmtVisitor : StatementTransformer
    {
      SimplifyInExprVisitor sv;
      ErrorReporter reporter;
      public SimplifyInStmtVisitor(ErrorReporter reporter, SimplifyInExprVisitor et):
        base(et) {
        this.sv = et;
        this.reporter = reporter;
      }

      public override Statement Visit(AssignStmt s, object st) {
        // Take care not to call the simplifier twice here; instead
        // call base method, assuming it'll simplify the right-hand side,
        // then extract the result
        var res = base.Visit(s, st);
        // to a simple variable
        var ie = s.Lhs as IdentifierExpr;
        // TODO: support patterns here
        if (ie == null) {
          return res;
        }
        // and the right-hand side is a simplifier call:
        var erhs = s.Rhs as ExprRhs;
        if (erhs == null || erhs.Expr == null || erhs.Expr.Resolved == null) {
          return res;
        }
        var fc = (s.Rhs as ExprRhs).Expr.Resolved as FunctionCallExpr;
        if (fc == null || !sv.IsSimplifierCall(fc)) {
          return res;
        }
        var simplified = res as AssignStmt;
        Contract.Assert(simplified != null && simplified.Rhs is ExprRhs);
        var newRhs = ((ExprRhs)simplified.Rhs).Expr;
        var msg =
          $"Adding local simplifier rule: {ie.Var.Name} |-> " +
          $"{Printer.ExprToString(newRhs)}";
        reporter.Info(MessageSource.Simplifier, s.Tok, msg);
        DebugMsg(msg);
        var varExpr = (new Cloner()).CloneExpr(ie) as IdentifierExpr;
        varExpr.DontUnify = true;
        sv.AddLocalRewriteRule(new RewriteRule(varExpr, newRhs));
        return simplified;
      }

    }

    protected Expression SimplifyInExpr(Expression e, bool inGhost) {
      var sv = new SimplifyInExprVisitor(reporter, simplifierFuncs, simplifierRules, inGhost);
      return sv.Visit(e, null);
    }

    internal Statement SimplifyInStmt(Statement stmt, bool inGhost) {
      var exprVis = new SimplifyInExprVisitor(reporter, simplifierFuncs, simplifierRules, inGhost);
      var stmtSimplifyVis = new SimplifyInStmtVisitor(reporter, exprVis);
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
            if (newBody != meth.Body) {
              DebugMsg($"New body for {meth.Name}: {Printer.StatementToString(newBody)}");
            }
            meth.Body = (BlockStmt)newBody;
          }
        }
      }
    }

    internal static long MeasureTime<T>(T t, Action<T> act) {
      var stopWatch = new Stopwatch();
      stopWatch.Start();
      act(t);
      stopWatch.Stop();
      return stopWatch.ElapsedMilliseconds;
    }

    internal override void PostResolve(ModuleDefinition m) {
      var time = MeasureTime(m, me => {
          FindSimplificationCallables(me);
          SimplifyCalls(me);
        });
      if (DafnyOptions.O.SimpTrace) {
        var msg = $"Simplification took {((double)time)/1000}s";
        reporter.Warning(MessageSource.Simplifier, m.BodyStartTok, msg);
        foreach (var item in PerfTimers.Timers) {
          long perc = item.Value.ElapsedMilliseconds / time;
          reporter.Warning(MessageSource.Simplifier, m.BodyStartTok,
                           $"Time spent in {item.Key}: {((double)(item.Value.ElapsedMilliseconds))/1000}s ({perc})");
        }

        DebugMsg($"~{PerfTimers.TriedRules} unsuccessful rule matching attempts");
        var ruleAvg = (PerfTimers.RuleAttempts.Count > 0 ? PerfTimers.RuleAttempts.Average() : 0);
        DebugMsg($"On average {ruleAvg}th rule matched");
        var avg = (PerfTimers.RuleFindingTimes.Count > 0 ? PerfTimers.RuleFindingTimes.Average() :
                   0);
        DebugMsg($"Identifying correct rule took {avg}ms on average");
        DebugMsg($"Performed {PerfTimers.RuleFindingTimes.Count} rewrites");
        var subTermAvg = (PerfTimers.MatchingSubtermNos.Count != 0 ?
                          PerfTimers.MatchingSubtermNos.Average() : 0);
        DebugMsg($"Rules match {subTermAvg}th subterm on average");
        DebugMsg($"Unification attemps: {PerfTimers.UnificationAttempts}");
        var univTime = PerfTimers.Timers[PerfTimers.UNIFICATION].ElapsedMilliseconds;
        double univAvg =
          (PerfTimers.UnificationAttempts != 0 ?
           ((double)univTime) / ((double)(PerfTimers.UnificationAttempts)) :
           0);
        DebugMsg($"Average unification time: {univAvg}ms");
        DebugMsg("## Rule Use");
        double numRules = PerfTimers.Rules.Values.Sum();
        foreach (var item in PerfTimers.Rules) {
          double perc = (numRules != 0 ? (item.Value / numRules) : 0);
          DebugMsg($"  {item.Key}: {item.Value} ({perc}%)");
        }
        var cnt = simplifierRules.Rules().Count();
        DebugMsg($"Number of simplification rules: {cnt}");
      }
    }
  }

  internal class DeclFinder : TopDownVisitor<HashSet<Declaration>>  {
    protected override bool VisitOneExpr(Expression e, ref HashSet<Declaration> st) {
      if (e is ConcreteSyntaxExpression) {
        return VisitOneExpr(e.Resolved, ref st);
      }
      var fc = e as FunctionCallExpr;
      var dv = e as DatatypeValue;
      if (fc != null) {
        st.Add(fc.Function);
      } else if (dv != null) {
        st.Add(dv.Ctor);
      }
      return true;
    }

    public static HashSet<Declaration> FindDecls(Expression e) {
      PerfTimers.StartTimer("FindDecls");
      var res = new HashSet<Declaration>();
      var dv = new DeclFinder();
      dv.Visit(e, res);
      PerfTimers.StopTimer("FindDecls");
      return res;
    }
  }

  internal class RuleSet {
    // internal Dictionary<Declaration, HashSet<RewriteRule>> declRules;
    // internal HashSet<RewriteRule> otherRules;

    internal List<RewriteRule> rules;
    internal ExpressionTagger tagger;
    public RuleSet() {
      // declRules = new Dictionary<Declaration, HashSet<RewriteRule>>();
      rules = new List<RewriteRule>();
      tagger = new ExpressionTagger();
    }

    public void AddRule(RewriteRule rr) {
      tagger.Visit(rr.Lhs, null);
      rules.Add(rr);
    }

    public void RemoveRule(RewriteRule rr) {
      rules.Remove(rr);
    }

    public IEnumerable<RewriteRule> Rules() {
      return rules;
    }

    public IEnumerable<RewriteRule> RulesFor(Expression e) {
      var decls = DeclFinder.FindDecls(e);
      return rules.OrderByDescending<RewriteRule, int>(rr => decls.Intersect(rr.LhsDecls).Count());
      // return rules;
    }

  }

  // This is a "summary" of the expression for unification
  // storing the outermost type of the expression and
  // its name if applicable
  internal abstract class ExpressionTag {
    public abstract String Name();
  }

  internal class DatatypeValueTag : ExpressionTag {
    DatatypeCtor ctor;
    public DatatypeValueTag(DatatypeCtor ctor) {
      this.ctor = ctor;
    }

    public override String Name() {
      return $"DatatypeValueTag({ctor.Name}[{ctor.GetHashCode()}]) [{this.GetHashCode()}]";
    }
  }

  internal class FunctionCallTag : ExpressionTag {
    Function f;
    public FunctionCallTag(Function f) {
      this.f = f;
    }
    public override String Name() {
      return $"FunctionCallTag({f.Name}[{f.GetHashCode()}]) [{this.GetHashCode()}]";
    }
  }

  internal class TagFactory {
    internal static Dictionary<DatatypeCtor, ExpressionTag> dtTags =
      new Dictionary<DatatypeCtor, ExpressionTag>();
    internal static Dictionary<Function, ExpressionTag> fcTags =
      new Dictionary<Function, ExpressionTag>();

    internal static V GetOrCreate<K, V>(Dictionary<K, V> dict, K k,
                                        Func<K, V> create) {
      V res;
      if (dict.TryGetValue(k, out res)) {
        return res;
      } else {
        res = create(k);
        dict[k] = res;
        return res;
      }
    }

    public static object TagExpression(Expression e) {
      var dv = e as DatatypeValue;
      var fc = e as FunctionCallExpr;
      if (dv != null) {
        return GetOrCreate(dtTags, dv.Ctor, ct => new DatatypeValueTag(ct));
      } else if (fc != null) {
        return GetOrCreate(fcTags, fc.Function, f => new FunctionCallTag(f));
      } else {
        if (!(e is IdentifierExpr)) {
          return e.GetType();
        }
      }
      return null;
    }
  }

  internal class ExpressionTagger : TopDownVisitor<object>
  {
    protected override bool VisitOneExpr(Expression e, ref object st) {
      if (e.Tag == null) {
        e.Tag = TagFactory.TagExpression(e);
        return true;
      } else {
        return true;
      }
    }
  }

  internal class RewriteRule {
    public readonly Expression Lhs;
    public readonly Expression Rhs;
    internal HashSet<Declaration> lhsDecls = null;
    public RewriteRule(Expression lhs, Expression rhs) {
      this.Lhs = lhs;
      this.Rhs = rhs;
    }

    public HashSet<Declaration> LhsDecls {
      get {
        if (lhsDecls != null) {
          return lhsDecls;
        }
        lhsDecls = DeclFinder.FindDecls(Lhs);
        return lhsDecls;
      }
    }
  }

  internal class PerfTimers
  {
    public const String FIND_RULE = "findRule";
    public const String LET_INLINING = "letInlining";
    public const String UNIFICATION = "unification";
    public static long TriedRules = 0;
    public static long UnificationAttempts = 0;
    public static List<long> RuleFindingTimes = new List<long>();
    public static List<long> MatchingSubtermNos = new List<long>();
    public static List<long> RuleAttempts = new List<long>();
    public static Dictionary<String, long> Rules = new Dictionary<String, long>();
    public static Dictionary<String, Stopwatch> Timers = new Dictionary<String, Stopwatch> {
      { FIND_RULE, new Stopwatch() },
      { LET_INLINING, new Stopwatch() },
      { UNIFICATION, new Stopwatch() }
    };

    internal static Stopwatch EnsureTimer(String s) {
      Stopwatch t;

      if (!Timers.TryGetValue(s, out t)) {
        var res = new Stopwatch();
        Timers.Add(s, res);
        return res;
      } else {
        return t;
      }
    }

    public static void RuleUse(String s) {
      if (!Rules.ContainsKey(s)) {
        Rules[s] = 1;
      } else {
        Rules[s]++;
      }
    }

    public static void StartTimer(String s) {
      EnsureTimer(s).Start();
    }

    public static void StopTimer(String s) {
      EnsureTimer(s).Stop();
    }

    public static long ElapsedMillis(String s) {
      return EnsureTimer(s).ElapsedMilliseconds;
    }

  }
}
