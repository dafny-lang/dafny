/* The Dafny Abstract Machine
 * This file specifies:
 * 1. A core language for Dafny based on call-by-push-value (CBPV) with
 *    state (mutable references), control (letcc/throw) for early returns, etc., and recursion 
 * 2. A novel CEK-machine interpreter that extends that of
 *    Hillerstrom-Lindley for fine-grain call-by-value
 * 3. A simple type system that is sound with respect to the interpreter
*/ 

module {:extern "DAM"} DAM {
  //import opened DafnyStdLibs.Wrappers

  // CBPV distinguishes between expressions and statements of positive and negative type, respectively
  module Syntax {
    datatype Option<A> = None | Some(value: A) {
      predicate IsFailure() { this.None? }
      function PropagateFailure<B>(): Option<B>
        requires IsFailure() { None }
      function Extract(): A
        requires !IsFailure() { this.value }
    }

    /*function Uncons<K(<), V>(m: map<K, V>): (K, V, map<K, V>) requires |m| > 0 {
        var k :| k in m && forall k' : K :: k <= k';
        (k, m[k], m - {k})
    }*/

    predicate Unique<V>(k: string, m: map<string, V>) {
      forall k' :: k' in m ==> k <= k'
    }

    lemma ExistsUnique<V>(m: map<string, V>)
      requires |m| > 0
      ensures exists k :: k in m && Unique(k, m)
      decreases |m|
    {
      var k :| k in m;
      var m' := m - {k};
      if |m'| == 0 {
        assert m == map[k := m[k]];
        assert Unique(k, m);
      } else {
        ExistsUnique(m');
        var k' :| k' in m' && Unique(k', m');
        if k <= k' {} else {}
        assert m == m'[k := m[k]];
      }
    }

    function mapOption<V(==)>(m: map<string, Option<V>>): Option<map<string, V>> decreases |m| {
      if |m| == 0 then
        Some(map[])
      else
        ExistsUnique(m);
        var k :| k in m && Unique(k, m);
        var v :- m[k];
        var m :- mapOption(m - {k});
        Some(m[k := v])
    }

    //method IsLeast

    class Ptr<A> {
      var deref: A
      constructor(expr: A) {
        deref := expr;
      }
    }

    type Field = string

    datatype Pos =
      Unit
    | Bool
    | Int
    | Thunk(neg: Neg)
    | Ref(pos: Pos)
    | Stack(start: Neg)

    datatype Neg =
      Value(pos: Pos)
    | Function(dom: Pos, cod: Neg)
    | Record(fields: map<Field, Neg>)

    type Var = string

    datatype Expr =
      Var(Var)
    | Unit
    | Bool(bool)
    | Int(int)
    // TODO datatypes
    | Thunk(Stmt)
    | Ref(Ptr<Val>)

    //Hamza-Voirol-Kuncak trick: annotate terms just enough so that ostensible checking terms synthesize
    datatype Stmt =
    // Value intro & elim
      Pure(Expr)
    | Bind(lhs: Stmt, var_: Var, rhs: Stmt)
    // Bool elim
    | Ite(guard: Expr, then_: Stmt, else_: Stmt)
    // Function intro & elim
    | Func(bound: Var, dom: Pos, body: Stmt)
    | Call(func: Stmt, arg: Expr)
    // Record intro & elim
    | Record(fields: map<Field, Stmt>)
    | Select(record: Stmt, field: Field)
    // Thunk elim
    | Force(Expr)
    // Ref elims
    | Read(ref: Expr, var_: Var, cont: Stmt)
    | Write(lvalue: Expr, rvalue: Expr, next: Stmt)
    // Print
    | Print(Expr, next: Stmt)
    // Recursion
    | Rec(bound: Var, body: Stmt)
    // Let-current-stack/letcc and throw
    | LetCS(bound: Var, body: Stmt)
    | Throw(stack: Expr, init: Stmt)
    // TODO calculate Heap of a comp

    // Let, which is notably distinct from Bind
    function Let(lhs: Expr, var_ : string, ty: Pos, rhs: Stmt): Stmt
      { Stmt.Call(Func(var_, ty, rhs), lhs) }
    
    // Imperative sequencing of commands (Stmts of Value(Unit) type)
    function Then(lhs: Stmt, rhs: Stmt): Stmt
      { Stmt.Bind(lhs, "_", rhs) }

    function Skip(): Stmt
      { Pure(Expr.Unit) }

    function While(guard: Stmt, body: Stmt, next: Stmt): Stmt {
      Rec("while", Stmt.Bind(guard, "if",
        Ite(Var("if"), Then(body, Force(Var("while"))), next)))
    }

    // The environment accumulates substitutions made along the course of machine execution, i.e.,
    // maps variables to values - closed intro. forms of positive type
    type Env = map<Var, Val>

    // To implement lexical scope, thunks and stacks are closures that save the environment they're defined in
    datatype Val =
      Unit
    | Bool(bool)
    | Int(int)
    | Thunk(Env, Stmt)
    | Ref(ptr: Ptr<Val>)
    | Stack(Env, Stack)

    // Stacks accumulate negative eliminations
    datatype Stack = Empty | Push(top: Frame, rest: Stack) {
      function Pop(): Option<(Frame, Stack)> {
        match this
        case Empty      => None
        case Push(t, r) => Some((t, r))
      }
    }

    datatype Frame =
      Bind(var_: Var, rhs: Stmt)
    | Call(arg: Expr)
    | Select(field: string)
  }

  module Machine {
    import opened Syntax

    // States of the CEK Machine
    type     In  = (Env, Stmt, Stack)
    datatype Out = Next(In) | Stuck | Terminal(Val)

    function Heap(state: In): set<Ptr<Val>> {
      set x : Val | x in state.0.Values && x.Ref? :: x.ptr
    }

    // Small-step semantics are divided between evaluation of expressions and stepping of the machine
    function Eval(env: Env, expr: Expr): Val {
      match expr
      case Var(x) =>
        // Type soundness will discharge this assumption
        assume {:axiom} x in env;
        env[x]
      case Unit     => Val.Unit
      case Bool(b)  => Val.Bool(b)
      case Int(i)   => Val.Int(i)
      // The Felleisen-Friedman trick: delay
      // substitution by constructing a closure
      case Thunk(c) => Val.Thunk(env, c)
      case Ref(ptr) => Val.Ref(ptr)
    }

    // TODO: ensures Preservation(in, out) = match out case In(next) => CheckCEK(g, next, start, end) | Stuck => false | Terminal(v) => CheckCEK(g, (env, ...), start, end)
    method Step(state: In) returns (out: Out) {
      var (env, comp, stack) := state;
      match comp
      case Bind(lhs, var_, rhs) =>
        return Next((env, lhs, Push(Frame.Bind(var_, rhs), stack)));
      
      case Pure(expr) => {
        match stack.Pop()
        case Some((Bind(var_, rhs), stack)) =>
          return Next((env[var_ := Eval(env, expr)], rhs, stack));
        case Some(_) => return Stuck;
        case None    => return Terminal(Eval(env, expr));
      }

      case Call(func, arg) =>
        return Next((env, func, Push(Frame.Call(arg), stack)));
      
      case Func(bound, _, body) => {
        match stack.Pop()
        case Some((Call(arg), stack)) =>
          return Next((env[bound := Eval(env, arg)], body, stack));
        case Some(_) => return Stuck;
        case None    => return Terminal(Val.Thunk(env, comp));
      }

      case Select(obj, field) =>
        return Next((env, obj, Push(Frame.Select(field), stack)));
      
      case Record(fields) => {
        match stack.Pop()
        case Some((Select(field), stack)) => {
          if case field in fields =>
               return Next((env, fields[field], stack));
             case true => return Stuck;
        }
        case Some(_) => return Stuck;
        case None    => return Terminal(Val.Thunk(env, comp));
      }

      case Ite(guard, then_, else_) => {
        match Eval(env, guard)
        case Bool(guard) =>
          return Next((env, if guard then then_ else else_, stack));
        
        case _ => return Stuck;
      }

      // Lexical scope restores the env of the closure
      case Force(thunk) => {
        match Eval(env, thunk)
        case Thunk(env, stmt) => return Next((env, stmt, stack));
        case _                => return Stuck;
      }

      case Read(ref, var_, next) => {
        match Eval(env, ref)
        case Ref(ptr) => return Next((env[var_ := ptr.deref], next, stack));
        case _        => return Stuck;
      }

      case Write(lval, rval, next) => {
        match Eval(env, lval)
        case Ref(ptr) =>
          //ptr.deref := Eval(env, rval);
          return Next((env, next, stack));
        case _        => return Stuck;
      }

      case Print(expr, next) =>
        print Eval(env, expr), "\n";
        return Next((env, next, stack));
      
      case Rec(self, body) =>
        return Next((env[self := Val.Thunk(env, comp)], body, stack));
      
      case LetCS(bound, body) =>
        return Next((env[bound := Val.Stack(env, stack)], body, stack));
      
      case Throw(stack, next) => {
        match Eval(env, stack)
        case Stack(env, stack) => return Next((env, next, stack));
        case _                 => return Stuck;
      }
    }

    //codatatype Trace = Next(In, Trace) | Stuck | Terminal(Val)
    // Coinductive big-step semantics a la Leroy
    method Run(s: In) decreases * {
      print("\n");
      var o := Step(s);
      match o
      case Next(s) => print(s, "\n"); Run(s);
      case _ => print "done/stuck\n"; return;
    }

    // Initial configuration
    function Initial(comp: Stmt): In
      { (map[], comp, Empty) }
  }

  module Typing {
    import opened Syntax

    type Context = map<Var, Pos>

    /*function SynthVal(v: Val): Option<Pos> decreases v, 2 {
      match v
      case Unit    => Some(Pos.Unit)
      case Bool(_) => Some(Pos.Bool)
      case Int(_)  => Some(Pos.Int)
      case Thunk(env, s) => (
        var g :- SynthEnv(env);
        var t :- SynthStmt(g, s);
        Some(Pos.Thunk(t))
      )
      case _   => None
    }*/

    predicate CheckExpr(g: Context, e: Expr, t: Pos) decreases e, 1 {
      SynthExpr(g, e) == Some(t)
    }

    predicate CheckStmt(g: Context, s: Stmt, t: Neg) decreases s, 1 {
      SynthStmt(g, s) == Some(t)
    }

    function SynthExpr(g: Context, expr: Expr): Option<Pos> decreases expr, 0 {
      match expr
      case Var(x)   => if x in g then Some(g[x]) else None
      case Unit     => Some(Pos.Unit)
      case Bool(_)  => Some(Pos.Bool)
      case Int(_)   => Some(Pos.Int)
      case Thunk(s) => (
        var t :- SynthStmt(g, s);
        Some(Pos.Thunk(t))
      )
      case Ref(p)   => None
    }

    function SynthStmt(g: Context, stmt: Stmt): Option<Neg> decreases stmt, 0 {
      match stmt
      case Pure(e) => (
        var t :- SynthExpr(g, e);
        Some(Neg.Value(t))
      )

      case Bind(lhs, var_, rhs) => (
        match SynthStmt(g, lhs)
        case Some(Value(t)) => SynthStmt(g[var_ := t], rhs)
        case _              => None
      )
      
      case Ite(guard, then_, else_) => (
        if CheckExpr(g, guard, Pos.Bool) then
          var t :- SynthStmt(g, then_);
          if CheckStmt(g, else_, t) then
            Some(t)
          else
            None
        else
          None
      )

      case Func(bound, dom, body) =>
        var cod :- SynthStmt(g[bound := dom], body);
        Some(Function(dom, cod))

      case Call(func, arg) => (
        match SynthStmt(g, func)
        case Some(Function(dom, cod)) =>
          if CheckExpr(g, arg, dom) then
            Some(cod)
          else
            None
        case _ => None
      )

      case Force(expr) => (
        match SynthExpr(g, expr)
        case Some(Thunk(t)) => Some(t)
        case _              => None
      )

      case Print(expr, next) =>
        var _ :- SynthExpr(g, expr);
        SynthStmt(g, next)

      case Record(fields) => (
        var fields :- mapOption(map field : Field | field in fields :: SynthStmt(g, fields[field]));
        Some(Neg.Record(fields))
      )

      case Select(record, field) => (
        match SynthStmt(g, record)
        case Some(Record(fields)) =>
          if field in fields then
            Some(fields[field])
          else
            None
        case _ => None
      )

      case _ => None
    }

    function SynthStack(g: Context, stack: Stack, start: Neg): Option<Neg> decreases stack, 0 {
      match stack
      case Empty => Some(start)
      case Push(Bind(var_, rhs), stack) => (
        match start
        case Value(t) => (
          match SynthStmt(g[var_ := t], rhs)
          case Some(start) => SynthStack(g, stack, start)
          case None        => None
        )
        case _        => None
      )

      case Push(Select(field), stack) => (
        match start
        case Record(fields) =>
          if field in fields then
            SynthStack(g, stack, fields[field])
          else
            None
        case _ => None
      )

      case Push(Call(arg), stack) => (
        match start
        case Function(dom, cod) =>
          if CheckExpr(g, arg, dom) then
            SynthStack(g, stack, cod)
          else
            None
        case _ => None
      )
    }
    /*function SynthEnv(e: Env): Option<Context> decreases e, 0 {
      mapOption(map x : Var | x in e :: SynthVal(e[x]))
    }*/
    /*
function SynthCEK(s: In): Option<Neg> {
    var (env, comp, stack) := s;
    match SynthEnv(env)
    case Some(g) => (
        match SynthStmt(g, comp)
        case Some(t) => SynthStack(g, stack, t)
        case None    => None
    )
    case None => None
}*/
  }

/*lemma Progress(g, s: In)
requires Check(g, s, t, start, end)
ensures  !Step(s).Stuck? {

}

CheckIn()

lemma Preservation(s: In)
requires var t := SynthCEK(s);
ensures CheckCEK(s, t)*/
}

/*method Main() decreases * {
    Run(Initial(
        Stmt.Bind(
            Pure(Expr.Bool(true)),
            "x",
            Ite(
                Var("x"),
                Pure(Expr.Bool(false)),
                Pure(Expr.Bool(true))
            )
        )
    ));
    // Verifies that lexical scope works
    var fc := Expr.Thunk(Func("y", Pos.Int, Pure(Var("x"))));
    var fv := Force(Var("f"));
    var x1 := Expr.Int(1);
    var x2 := Expr.Int(2);
    var z  := Expr.Int(0);
    Run(Initial(
        Let(x1, "x", Pos.Int,
        Let(fc, "f", Pos.Int,
        Let(x2, "x", Pos.Int,
        Stmt.Call(fv, z))))
    ));
}*/