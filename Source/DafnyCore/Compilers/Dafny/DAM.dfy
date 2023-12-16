/* The Dafny Abstract Machine
 * This file specifies:
 * 1. A core language for Dafny based on call-by-push-value (CBPV) with
 *    state (mutable references), control (letcc/throw) for early returns, etc., and recursion 
 * 2. A novel CESK-machine interpreter that extends the CK machine for CBPV
 * 3. A simple type system that is sound with respect to the interpreter
*/ 

module {:extern "DAM"} DAM {
  module Utils {
    datatype Option<A> = None | Some(value: A) {
      predicate IsFailure() { this.None? }
      function PropagateFailure<B>(): Option<B>
        requires IsFailure() { None }
      function Extract(): A
        requires !IsFailure() { this.value }
      function GetOr(default: A): A {
        match this
        case Some(v) => v
        case None    => default
      }
    }

    function SeqGet<A>(s: seq<A>, idx: nat): Option<A> {
      if idx < |s| then Some(s[idx]) else None
    }

    function UpdateSeq<A>(s: seq<A>, idx: nat, val: A): seq<A>
      requires idx <= |s|
    {
      if idx < |s| then s[idx := val] else s + [val]
    }

    function Extend<A>(s: seq<A>, elt: A): (nat, seq<A>) {
      (|s|, s + [elt])
    }

    function mapGet<K, V>(m: map<K, V>, k: K): Option<V> {
      if k in m then Some(m[k]) else None
    }

    function mapOption<K, V>(m: map<K, Option<V>>): Option<map<K, V>> {
      if forall k <- m :: m[k].Some? then Some(map k <- m :: m[k].Extract()) else None
    }
  }

  // CBPV distinguishes between expressions and statements of positive and negative type, respectively
  module Syntax {
    import opened Utils

    type Field = string

    datatype Pos =
      Unit
    | Bool
    | Int
    | Thunk(neg: Neg)
    | Ref(ref: Pos)
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
    // Ref intro & elims
    | New(init: Expr, var_: Var, next: Stmt)
    | Read(ref: Expr, var_: Var, next: Stmt)
    | Write(lvalue: Expr, rvalue: Expr, next: Stmt)
    // Print
    | Print(Expr, next: Stmt)
    // Recursion
    | Rec(bound: Var, body: Stmt)
    // Let-current-stack/letcc and throw
    | LetCS(bound: Var, body: Stmt)
    | Throw(stack: Expr, next: Stmt)

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
  }

  module Machine {
    import opened Syntax
    import opened Utils
    
    type Addr = nat

    // The environment accumulates substitutions made along the course of machine execution, i.e.,
    // maps variables to addresses
    type Env = map<Var, Addr>

    // The store maps addresses to values - closed intro. forms of positive type
    type Store = seq<Val>

    // Closed expressions are evaluated into values
    type ClosedExpr = (Env, Expr)

    // Closed statements - closed expressions that are thunks
    type ClosedStmt = (Env, Stmt)
    
    datatype Val =
      Unit
    | Bool(answer: bool)
    | Int(int)
    // To implement lexical scope, thunks are closures
    | Thunk(closure: ClosedStmt)
    | Ref(addr: Addr)
    | Stack(stack: Stack)

    // Stacks accumulate negative eliminations
    datatype Stack = Empty | Push(top: Frame, rest: Stack) {
      function Pop(): Option<(Frame, Stack)> {
        match this
        case Empty      => None
        case Push(t, r) => Some((t, r))
      }
    }

    datatype Frame =
      // Note: var_ can be free in rhs, so it's not closed entirely
      Bind(var_: Var, rhs: ClosedStmt)
    | Call(arg: ClosedExpr)
    | Select(field: Field)

    // States of the CESK Machine
    type     Input  = (Store, ClosedStmt, Stack)
    datatype Output = Next(Input) | Terminal
  }

  module Statics {
    import opened Utils
    import opened Syntax
    import opened Machine

    // Honestly, I forgot why this is an alist
    type Context = map<Var, Pos>

    // G |- expr => t+
    function SynthExpr(g: Context, expr: Expr): Option<Pos> decreases expr, 0 {
      match expr
      case Var(x)   => mapGet(g, x)
      case Unit     => Some(Pos.Unit)
      case Bool(_)  => Some(Pos.Bool)
      case Int(_)   => Some(Pos.Int)
      case Thunk(s) =>
        var t :- SynthStmt(g, s);
        Some(Pos.Thunk(t))
    }

    // G |- expr <= t+
    predicate CheckExpr(g: Context, e: Expr, t: Pos) decreases e, 1 {
      SynthExpr(g, e) == Some(t)
    }

    // G |- stmt => t-
    function SynthStmt(g: Context, stmt: Stmt): Option<Neg> decreases stmt, 0 {
      match stmt
      case Pure(e) =>
        var t :- SynthExpr(g, e);
        Some(Neg.Value(t))

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

      case Record(fields) =>
        var fields :- mapOption(map lbl <- fields :: SynthStmt(g, fields[lbl]));
        Some(Neg.Record(fields))

      case Select(record, lbl) => (
        match SynthStmt(g, record)
        case Some(Record(fields)) =>
          mapGet(fields, lbl)
        case _ => None
      )

      case New(init, var_, next) =>
        var t :- SynthExpr(g, init);
        SynthStmt(g[var_ := Pos.Ref(t)], next)

      case Read(ref, var_, next) => (
        match SynthExpr(g, ref)
        case Some(Ref(t)) => SynthStmt(g[var_ := t], next)
        case _            => None
      )

      case Write(lhs, rhs, next) => (
        match SynthExpr(g, lhs)
        case Some(Ref(t)) =>
          if CheckExpr(g, rhs, t) then
            SynthStmt(g, next)
          else
            None
        case _            => None
      )
      
      case _ => None
    }

    // G |- stmt <= t-
    predicate CheckStmt(g: Context, stmt: Stmt, t: Neg) decreases stmt, 1 {
      SynthStmt(g, stmt) == Some(t)
    }

    // S |- env => G
    // rewrite in terms of maps? []
    function SynthEnv(s: StoreTyping, env: Env): Option<Context> decreases env {
      mapOption(map var_ <- env :: SeqGet(s, env[var_]))
    }

    // S |- env <= G
    predicate CheckEnv(s: StoreTyping, env: Env, g: Context) {
      SynthEnv(s, env) == Some(g)
    }

    // S |- (env, expr) => t+
    function SynthClosedExpr(s: StoreTyping, expr: ClosedExpr): Option<Pos> {
      var (env, expr) := expr;
      var g :- SynthEnv(s, env);
      SynthExpr(g, expr)
    }

    // S |- (env, expr) <= t+
    predicate CheckClosedExpr(s: StoreTyping, expr: ClosedExpr, t: Pos) {
      SynthClosedExpr(s, expr) == Some(t)
    }

    lemma CheckClosedExprWeakening(s: StoreTyping, s': StoreTyping, expr: ClosedExpr, t: Pos)
      requires CheckClosedExpr(s, expr, t)
      requires s <= s'
      ensures  CheckClosedExpr(s', expr, t)

    // S |- (env, stmt) => t-
    function SynthClosedStmt(s: StoreTyping, stmt: ClosedStmt): Option<Neg> {
      var (env, stmt) := stmt;
      var g :- SynthEnv(s, env);
      SynthStmt(g, stmt)
    }

    // S |- start- => stack => end-
    function SynthStack(s: StoreTyping, start: Neg, stack: Stack): Option<Neg> decreases stack {
      match stack
      case Empty => Some(start)
      case Push(Bind(var_, (env, rhs)), stack) => (
        match start
        case Value(t) =>
          var g :- SynthEnv(s, env);
          var start :- SynthStmt(g[var_ := t], rhs);
          SynthStack(s, start, stack)
        case _        => None
      )

      case Push(Select(lbl), stack) => (
        match start
        case Record(fields) =>
          var start :- mapGet(fields, lbl);
          SynthStack(s, start, stack)
        case _ => None
      )

      case Push(Call(arg), stack) => (
        match start
        case Function(dom, cod) =>
          if CheckClosedExpr(s, arg, dom) then
            SynthStack(s, cod, stack)
          else
            None
        case _ => None
      )
    }

    // S |- stack <= start- <= end-
    predicate CheckStack(s: StoreTyping, start: Neg, stack: Stack, end: Neg) {
      SynthStack(s, start, stack) == Some(end)
    }

    lemma CheckStackWeakening(s: StoreTyping, s': StoreTyping, start: Neg, stack: Stack, end: Neg)
      requires s <= s'
      requires CheckStack(s, start, stack, end)
      ensures CheckStack(s', start, stack, end)

    type StoreTyping = seq<Pos>

    // S |- val => t+
    function SynthVal(s: StoreTyping, val: Val): Option<Pos> decreases val {
      match val
      case Unit        => Some(Pos.Unit)
      case Bool(_)     => Some(Pos.Bool)
      case Int(_)      => Some(Pos.Int)
      case Thunk(stmt) =>
        var t :- SynthClosedStmt(s, stmt);
        Some(Pos.Thunk(t))
      case Ref(addr) =>
        var t :- SeqGet(s, addr);
        Some(Pos.Ref(t))
      case Stack(_) => None
      /*var end :- SynthStack(s, start, stack);
        Some(Pos.Stack(end)) */
    }

    // S |- val <= t+
    predicate CheckVal(s: StoreTyping, val: Val, t: Pos) {
      SynthVal(s, val) == Some(t)
    }

    lemma CheckValWeakening(s: StoreTyping, s': StoreTyping, val: Val, t: Pos)
      requires s <= s'
      requires CheckVal(s, val, t)
      ensures CheckVal(s', val, t)
    
    // sto |- S
    predicate CheckStore(s: StoreTyping, store: Store) {
      // We want |store| == |s| so that extensions s'
      // to s allow CheckStack, etc. to admit weakening on s'
      // (they wouldn't if s instead were *updated* in case |store| < |s|)
      // downside: CheckInput/Output don't admit weakening on s
      |store| == |s| && forall addr | 0 <= addr < |store| :: CheckVal(s, store[addr], s[addr])
    }

    // S |- input => end
    function SynthInput(s: StoreTyping, input: Input): Option<Neg> {
      var (sto, stmt, stack) := input;
      if CheckStore(s, sto) then
        var start :- SynthClosedStmt(s, stmt);
        var end :- SynthStack(s, start, stack);
        Some(end)
      else
        None
    }

    // S |- input <= end
    predicate CheckInput(s: StoreTyping, input: Input, end: Neg) {
      SynthInput(s, input) == Some(end)
    }

    // S |- output <= end
    predicate CheckOutput(s: StoreTyping, out: Output, end: Neg) {
      match out
      case Next(next) => CheckInput(s, next, end)
      case Terminal   => true
    }
  }

  module Dynamics {
    import opened Utils
    import opened Syntax
    import opened Machine
    import opened Statics

    // Well-typed reference allocation and initialization
    lemma UpdateStore(s: StoreTyping, store: Store, val : Val, t: Pos)
      requires CheckStore(s, store)
      requires CheckVal(s, val, t)
      ensures  var (addr, store') := Extend(store, val);
               var (addr', s')    := Extend(s, t);
               addr == addr' && CheckStore(s', store')
    
    // Well-typed updates to the environment
    lemma UpdateEnv(s: StoreTyping, env: Env, g: Context, var_: Var, t: Pos)
      requires CheckEnv(s, env, g)
      // This is true even when var_ shadows an existing binding in env/g
      ensures
        var (addr, s') := Extend(s, t);
        CheckEnv(s', env[var_ := addr], g[var_ := t])

    // Big-step evaluation of expressions
    function Eval(ghost s: StoreTyping, store: Store, expr: ClosedExpr, ghost t: Pos): (output: Val)
      requires CheckStore(s, store)        // S |- sto
      requires CheckClosedExpr(s, expr, t) // S |- expr <= t
      ensures  CheckVal(s, output, t)      // S |- output <= t
    {
      var (env, expr) := expr;
      match expr
      case Var(x)      => store[env[x]]
      case Unit        => Val.Unit
      case Bool(b)     => Val.Bool(b)
      case Int(i)      => Val.Int(i)
      case Thunk(stmt) => Val.Thunk((env, stmt))
    }

    // Small-step reduction for the CESK machine
    // Progress = totality, preservation = requires + ensures clause
    function Step(ghost s: StoreTyping, input: Input, ghost end: Neg): (output: Output)
      requires CheckInput(s, input, end)
      // s <= s' b/c no deallocations occur...for now!
      ensures  exists s' | s <= s' :: CheckOutput(s', output, end)
    {
      var (store, (env, stmt), stack) := input;

      assert CheckStore(s, store);
      ghost var g     := SynthEnv(s, env).Extract();
      ghost var start := SynthStmt(g, stmt).Extract();
      ghost var end   := SynthStack(s, start, stack).Extract();

      match stmt
      case Ite(guard, then_, else_) =>
        var val := Eval(s, store, (env, guard), Pos.Bool);
        var output := Next((store, (env, if val.answer then then_ else else_), stack));
        assert CheckOutput(s, output, end);
        output
      
      case Bind(lhs, var_, rhs) =>
        var output := Next((store, (env, lhs), Push(Frame.Bind(var_, (env, rhs)), stack)));
        assert CheckOutput(s, output, end);
        output
      
      case Pure(expr) => (
        match stack.Pop()
        case Some((Bind(var_, (env', rhs)), stack)) =>
          ghost var t := start.pos;
          var val := Eval(s, store, (env, expr), t);

          var (addr, store') := Extend(store, val);
          ghost var (_, s') := Extend(s, t);
          UpdateStore(s, store, val, t);

          ghost var g := SynthEnv(s, env').Extract();
          UpdateEnv(s, env', g, var_, t);

          CheckStackWeakening(s, s', SynthStmt(g[var_ := t], rhs).Extract(), stack, end);

          var output := Next((store', (env'[var_ := addr], rhs), stack));
          assert CheckOutput(s', output, end);
          output
        case None =>
          var output := Terminal;
          assert CheckOutput(s, output, end);
          output
      )

      // Lexical scope restores the closure
      case Force(thunk) =>
        var val := Eval(s, store, (env, thunk), Pos.Thunk(start));
        var output := Next((store, val.closure, stack));
        assert CheckOutput(s, output, end);
        output
    
      case Call(func, arg) =>
        var output := Next((store, (env, func), Push(Frame.Call((env, arg)), stack)));
        assert CheckOutput(s, output, end);
        output
      
      case Func(bound, _, body) => (
        match stack.Pop()
        case Some((Call(arg), stack)) =>
          ghost var dom := start.dom;
          var val := Eval(s, store, arg, dom);

          var (addr, store') := Extend(store, val);
          ghost var (_, s') := Extend(s, dom);
          UpdateStore(s, store, val, dom);

          UpdateEnv(s, env, g, bound, dom);
          
          CheckStackWeakening(s, s', start.cod, stack, end);

          var output := Next((store', (env[bound := addr], body), stack));
          assert CheckOutput(s', output, end);
          output
        case None =>
          var output := Terminal;
          assert CheckOutput(s, output, end);
          output
      )

      case Select(record, field) =>
        var output := Next((store, (env, record), Push(Frame.Select(field), stack)));
        assert CheckOutput(s, output, end);
        output

      case Record(fields) => (
        match stack.Pop()
        case Some((Select(lbl), stack)) =>
          var output := Next((store, (env, fields[lbl]), stack));
          assert CheckOutput(s, output, end);
          output
        
        case None =>
          var output := Terminal;
          assert CheckOutput(s, output, end);
          output
      )

      case Print(expr, next) =>
        ghost var t := SynthExpr(g, expr).Extract();
        var val := Eval(s, store, (env, expr), t);
        //print val, "\n";
        var output := Next((store, (env, next), stack));
        assert CheckOutput(s, output, end);
        output
      
      case New(init, var_, next) => (
        ghost var t := SynthExpr(g, init).Extract();
        var val := Eval(s, store, (env, init), t);
        
        var (addr1, store1) := Extend(store, val);
        var (addr2, store2) := Extend(store1, Val.Ref(addr1));

        ghost var (_, s1) := Extend(s, t);
        ghost var (_, s2) := Extend(s1, Pos.Ref(t));

        UpdateStore(s, store, val, t);
        UpdateStore(s1, store1, Val.Ref(addr1), Pos.Ref(t));
        
        assert CheckEnv(s, env, g);
        assume CheckEnv(s1, env, g);
        UpdateEnv(s1, env, g, var_, Pos.Ref(t));

        CheckStackWeakening(s, s2, start, stack, end);

        var output := Next((store2, (env[var_ := addr2], next), stack));
        assert CheckOutput(s2, output, end);
        output
      )

      case Write(lhs, rhs, next) => (
        var tl := SynthExpr(g, lhs).Extract();
        var tr := SynthExpr(g, rhs).Extract();

        var lval := Eval(s, store, (env, lhs), tl).addr;
        var rval := Eval(s, store, (env, rhs), tr);

        var output := Next((store[lval := rval], (env, next), stack));
        assert CheckOutput(s, output, end);
        output
      )

      /*case Read(ref, var_, next) => (
        ghost var t := SynthExpr(g, ref).Extract();
        var addr := Eval(s, store, (env, ref), t).addr;
        
        var (addr', store') := Extend(store, env[addr]);

        ghost var (_, s') := Extend(s, t.ref);

        UpdateStore(s, store, val, t);
        
        assert CheckEnv(s, env, g);
        assume CheckEnv(s1, env, g);
        UpdateEnv(s1, env, g, var_, Pos.Ref(t));

        CheckStackWeakening(s, s2, start, stack, end);

        var output := Next((store2, (env[var_ := addr2], next), stack));
        assert CheckOutput(s2, output, end);
        output
      )*/

      case _ =>
        var output := Terminal;
        assert CheckOutput(s, output, end);
        output
      
      /*
      case Rec(self, body) =>
        return Next((Update(self, Val.Thunk(env, comp), env), body, stack));
      
      case LetCS(bound, body) =>
        return Next((Update(bound, Val.Stack(env, stack), env), body, stack));
      
      case Throw(stack, next) => {
        match Eval(env, stack)
        case Some(Stack(env, stack)) => return Next((env, next, stack));
        case _                       => return Stuck;
      }*/
    }

    // Leroy-style executable big-step semantics for the machine
    codatatype Trace = Stepping(Input, Trace) | Done

    function Run(ghost s: StoreTyping, input: Input, ghost end: Neg): Trace
      requires CheckInput(s, input, end)
    {
      match Step(s, input, end)
      case Next(next) =>
        ghost var s' :| CheckInput(s', next, end);
        Stepping(next, Run(s', next, end))
      case Terminal   => Done
    }

    // Initial configuration
    function Initial(stmt: Stmt): Input
      { ([], (map[], stmt), Stack.Empty) }
  }
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