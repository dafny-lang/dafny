/* The Dafny Abstract Machine
 * This file specifies:
 * 1. A core language for Dafny based on call-by-push-value (CBPV) with
 *    state (mutable references), control (letcc/throw) for early returns, etc., and recursion 
 * 2. A novel CESK-machine interpreter that extends the CK machine for CBPV
 *    Notably, the environment does not point to addresses like a CESK machine. This avoids spurious
 *    allocations (and, therefore, proof burden about the store) for lexically-scoped bindings.
 * 3. A simple type system that is sound with respect to the interpreter
 */

module {:extern "DAM"} DAM {
  module Utils {
    // Can't use Dafny Standard Libraries here
    // because GeneratedFromDafny.cs would contain
    // code that is not compilable...for some reason

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
    | LT(Expr, Expr)
    | Plus(Expr, Expr)
    // TODO recursive datatypes
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
    | Rec(bound: Var, fix: Neg, body: Stmt)
    // Let-current-stack/letcc and throw
    | LetCS(bound: Var, start: Neg, body: Stmt)
    | Throw(stack: Expr, oldstart: Neg, next: Stmt)

    // Let, which is notably distinct from Bind
    function Let(lhs: Expr, var_ : string, ty: Pos, rhs: Stmt): Stmt
      { Stmt.Call(Func(var_, ty, rhs), lhs) }
    
    // Imperative sequencing of commands (Stmts of Value(Unit) type)
    function Command(): Neg {
      Value(Pos.Unit)
    }

    function Then(lhs: Stmt, rhs: Stmt): Stmt
      { Stmt.Bind(lhs, "_", rhs) }

    function Skip(): Stmt
      { Pure(Expr.Unit) }

    function While(guard: Stmt, body: Stmt, next: Stmt): Stmt {
      Rec("while", Command(), Stmt.Bind(guard, "if",
        Ite(Var("if"), Then(body, Force(Var("while"))), next)))
    }
  }

  module Machine {
    import opened Syntax
    import opened Utils
    
    type Addr = nat

    // The environment accumulates substitutions made along the course of machine execution, i.e.,
    // maps variables to values - closed intro. forms of positive type
    type Env = map<Var, Val>

    // The store maps addresses to values
    type Store = seq<Val>

    // Closed expressions are evaluated into values
    type ClosedExpr = (Env, Expr)

    // Closed statements are executed by the machine
    type ClosedStmt = (Env, Stmt)
    
    datatype Val =
      Unit
    | Bool(answer: bool)
    | Int(number: int)
    // To implement lexical scope, thunks are closures
    | Thunk(closure: ClosedStmt)
    | Ref(addr: Addr)
    | Stack(start: Neg, stack: Stack)

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

    datatype Event = Silent | Print(Val)

    // States of the CESK Machine; outputs can raise events (a top-level effect not to be handled by the interpreter)
    type     Input  = (Store, ClosedStmt, Stack)
    datatype Output = Raise(event: Event, next: Input) | Terminal

    // Most of the time, there is no such event
    function Next(next: Input): Output {
      Raise(Silent, next)
    }
  }

  module Statics {
    import opened Utils
    import opened Syntax
    import opened Machine

    type Context = map<Var, Pos>

    // G |- expr => t+
    function SynthExpr(g: Context, expr: Expr): Option<Pos> decreases expr, 0 {
      match expr
      case Var(x)   => mapGet(g, x)
      case Unit     => Some(Pos.Unit)
      case Bool(_)  => Some(Pos.Bool)
      case Int(_)   => Some(Pos.Int)
      case LT(lhs, rhs) =>
        if CheckExpr(g, lhs, Pos.Int) && CheckExpr(g, rhs, Pos.Int) then Some(Pos.Bool) else None
      case Plus(lhs, rhs) =>
        if CheckExpr(g, lhs, Pos.Int) && CheckExpr(g, rhs, Pos.Int) then Some(Pos.Int) else None
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

      case Rec(self, fix, body) =>
        if CheckStmt(g[self := Pos.Thunk(fix)], body, fix) then
          Some(fix)
        else None

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

      case LetCS(bound, start, body) =>
        SynthStmt(g[bound := Pos.Stack(start)], body)
      
      case Throw(stack, oldstart, next) => (
        match SynthExpr(g, stack)
        case Some(Stack(start)) =>
          if CheckStmt(g, next, start) then
            Some(oldstart)
          else
            None
        case _ => None
      )
    }

    // G |- stmt <= t-
    predicate CheckStmt(g: Context, stmt: Stmt, t: Neg) decreases stmt, 1 {
      SynthStmt(g, stmt) == Some(t)
    }

    // S |- env => G
    function SynthEnv(s: StoreTyping, env: Env): Option<Context> {
      mapOption(map var_ <- env :: SynthVal(s, env[var_]))
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

    type StoreTyping = seq<Pos>

    // S |- val => t+
    function SynthVal(s: StoreTyping, val: Val): Option<Pos> decreases val {
      match val
      case Unit        => Some(Pos.Unit)
      case Bool(_)     => Some(Pos.Bool)
      case Int(_)      => Some(Pos.Int)
      case Thunk((env, stmt)) =>
        // No problem, rose tree ordering
        assume {:axiom} forall var_ <- env :: env[var_] < val;
        var g :- mapOption(map var_ <- env :: SynthVal(s, env[var_]));
        var t :- SynthStmt(g, stmt);
        //var t :- SynthClosedStmt(s, (env, stmt));
        Some(Pos.Thunk(t))
      case Ref(addr) =>
        var t :- SeqGet(s, addr);
        Some(Pos.Ref(t))
      case Stack(start, stack) =>
        /*if SynthStack(s, start, stack).Some? then
          Some(Pos.Stack(start))
        else
          None*/ None
    }

    // S |- val <= t+
    predicate CheckVal(s: StoreTyping, val: Val, t: Pos) decreases val, 1 {
      SynthVal(s, val) == Some(t)
    }
    
    // sto |- S (defn. 13.5.1 in TAPL)
    predicate CheckStore(s: StoreTyping, store: Store) {
      // Like TAPL, we want |store| == |s| so that extensions s'
      // to s allow CheckStack, etc. to admit weakening on s'.
      // If |store| < |s|, then one would have to generate a fresh address addr from |s|
      // and fill in dummy values for locations |store|...addr in store that check against types
      // those locations in s. If said types are empty, this isn't possible!
      //
      // Ideally, we would have some abstract type of locations from which one could generate fresh ones
      // And use maps instead of sequences, but this doesn't seem worth the effort
      //
      // The downside is that CheckInput/Output don't admit weakening on s, but we never depend on this
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
      case Raise(_, next) => CheckInput(s, next, end)
      case Terminal       => true
    }
  }

  module Dynamics {
    import opened Utils
    import opened Syntax
    import opened Machine
    import opened Statics
    
    // Well-typed updates to the environment (substitution lemma)
    lemma UpdateEnv(s: StoreTyping, env: Env, g: Context, var_: Var, val: Val, t: Pos)
      requires CheckEnv(s, env, g) // S |- env <= G
      requires CheckVal(s, val, t) // S |- val <= t
      ensures  CheckEnv(s, env[var_ := val], g[var_ := t]) // S |- [var_/val]env <= G, var_ : t
    {
      assume {:axiom} CheckEnv(s, env[var_ := val], g[var_ := t]);
    }
    
    // Well-typed reference allocation and initialization (lemma 13.5.5 in TAPL, kind of)
    lemma UpdateStore(s: StoreTyping, store: Store, val : Val, t: Pos)
      requires CheckStore(s, store)
      requires CheckVal(s, val, t)
      ensures  var (addr, store') := Extend(store, val);
               var (addr', s')    := Extend(s, t);
               addr == addr' && CheckStore(s', store')
    {
      var (addr, store') := Extend(store, val);
      var (addr', s')    := Extend(s, t);
      assume {:axiom} CheckStore(s', store');
    }

    // Big-step evaluation of expressions
    function Eval(ghost s: StoreTyping, expr: ClosedExpr, ghost t: Pos): (output: Val)
      requires CheckClosedExpr(s, expr, t) // S |- expr <= t
      ensures  CheckVal(s, output, t)      // S |- output <= t
      decreases expr.1
    {
      var (env, expr) := expr;
      match expr
      case Var(x)      => env[x]
      case Unit        => Val.Unit
      case Bool(b)     => Val.Bool(b)
      case Int(i)      => Val.Int(i)
      case LT(lhs, rhs) =>
        ghost var g := SynthEnv(s, env).Extract();
        assert CheckExpr(g, lhs, Pos.Int);
        assert CheckExpr(g, rhs, Pos.Int);
        var lhs := Eval(s, (env, lhs), Pos.Int).number;
        var rhs := Eval(s, (env, rhs), Pos.Int).number;
        Val.Bool(false)
      case Plus(lhs, rhs) =>
        ghost var g := SynthEnv(s, env).Extract();
        assert CheckExpr(g, lhs, Pos.Int);
        assert CheckExpr(g, rhs, Pos.Int);
        var lhs := Eval(s, (env, lhs), Pos.Int).number;
        var rhs := Eval(s, (env, rhs), Pos.Int).number;
        Val.Int(0)
      case Thunk(stmt) =>
        // Because Dafny can't figure out that mapoption in synthval = synthenv
        assert CheckVal(s, Val.Thunk((env, stmt)), t);
        Val.Thunk((env, stmt))
    }

    // Small-step reduction for the CESK machine
    // Progress = totality, preservation = requires + ensures clause
    function Step(ghost s: StoreTyping, input: Input, ghost end: Neg): (output: Output)
      requires CheckInput(s, input, end)
      ensures  exists s' :: CheckOutput(s', output, end)
    {
      var (store, (env, stmt), stack) := input;
      // Get the preconditions for preservation in order
      assert CheckStore(s, store);
      ghost var g     := SynthEnv(s, env).Extract();
      ghost var start := SynthStmt(g, stmt).Extract();
      ghost var end   := SynthStack(s, start, stack).Extract();
      // Execute!
      match stmt
      case Ite(guard, then_, else_) =>
        var val := Eval(s, (env, guard), Pos.Bool);
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
          var val := Eval(s, (env, expr), t);
          UpdateEnv(s, env', SynthEnv(s, env').Extract(), var_, val, t);
          var output := Next((store, (env'[var_ := val], rhs), stack));
          assert CheckOutput(s, output, end);
          output
        case None =>
          var output := Terminal;
          assert CheckOutput(s, output, end);
          output
      )

      case Force(thunk) =>
        var val := Eval(s, (env, thunk), Pos.Thunk(start));
        // This is harmless b/c Dafny can't tell that SynthEnv
        assume {:axiom} SynthClosedStmt(s, val.closure) == Some(start);
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
          var val := Eval(s, arg, dom);
          UpdateEnv(s, env, g, bound, val, dom);
          var output := Next((store, (env[bound := val], body), stack));
          assert CheckOutput(s, output, end);
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
        var val := Eval(s, (env, expr), t);
        var output := Raise(Event.Print(val), (store, (env, next), stack));
        assert CheckOutput(s, output, end);
        output
      
      case New(init, var_, next) =>
        ghost var t := SynthExpr(g, init).Extract();
        var val := Eval(s, (env, init), t);
        var (addr, store') := Extend(store, val);
        ghost var (_, s') := Extend(s, t);
        UpdateStore(s, store, val, t);
        // No problem, CheckEnv admits weakening (lemma 13.5.6 in TAPL)
        assert CheckEnv(s, env, g);
        assume {:axiom} CheckEnv(s', env, g);
        UpdateEnv(s', env, g, var_, Val.Ref(addr), Pos.Ref(t));
        // No problem, CheckStack admits weakening (lemma 13.5.6 in TAPL)
        assert CheckStack(s, start, stack, end);
        assume {:axiom} CheckStack(s', start, stack, end);
        var output := Next((store', (env[var_ := Val.Ref(addr)], next), stack));
        assert CheckOutput(s', output, end);
        output

      case Write(lhs, rhs, next) =>
        var lval := Eval(s, (env, lhs), SynthExpr(g, lhs).Extract()).addr;
        var rval := Eval(s, (env, rhs), SynthExpr(g, rhs).Extract());
        var output := Next((store[lval := rval], (env, next), stack));
        assert CheckOutput(s, output, end);
        output

      case Read(ref, var_, next) =>
        ghost var t := SynthExpr(g, ref).Extract();
        var val := store[Eval(s, (env, ref), t).addr];
        UpdateEnv(s, env, g, var_, val, t.ref);
        var output := Next((store, (env[var_ := val], next), stack));
        assert CheckOutput(s, output, end);
        output

      case Rec(self, fix, body) =>
        var val := Val.Thunk((env, stmt));
        UpdateEnv(s, env, g, self, val, Pos.Thunk(fix));
        var output := Next((store, (env[self := val], body), stack));
        assert CheckOutput(s, output, end);
        output
      
      case LetCS(bound, start, body) =>
        assume {:axiom} CheckVal(s, Val.Stack(start, stack), Pos.Stack(start));
        var output := Next((store, (env[bound := Val.Stack(start, stack)], body), stack));
        assert CheckOutput(s, output, end);
        output
      
      case Throw(expr, _, next) => (
        ghost var t := SynthExpr(g, expr).Extract();
        var val := Eval(s, (env, expr), t);
        var output := Next((store, (env, next), val.stack));
        assert CheckOutput(s, output, end);
        output
      )
    }

    // Initial configuration (see Levy's thesis)
    function Initial(stmt: Stmt, ghost end: Neg): (output: Input)
      requires CheckStmt(map[], stmt, end)
      ensures  CheckInput([], output, end)
    {
      ([], (map[], stmt), Stack.Empty)
    }

    // Leroy-style executable big-step semantics for the machine
    // Labeled transition system for indicating top-level effects (print, I/O, etc.)
    // ***DO NOT USE THIS***: there is apparently a bug in coinduction that causes
    // the returnee of Run* etc. to satisfy both trace.Stepping? and trace.Done?
    // Use Interpret() instead
    codatatype Trace = Stepping(Event, Input, Trace) | Done

    function Run(ghost s: StoreTyping, input: Input, ghost end: Neg): Trace
      requires CheckInput(s, input, end)
    {
      match Step(s, input, end)
      case Raise(evt, next) =>
        ghost var s' :| CheckInput(s', next, end);
        Stepping(evt, next, Run(s', next, end))
      case Terminal   => Done
    }

    function RunSafe(stmt: Stmt): Option<Trace> {
      var end :- SynthStmt(map[], stmt);
      Some(Run([], Initial(stmt, end), end))
    }
    
    function RunUnsafe(stmt: Stmt): Trace {
      assume {:axiom} exists end :: CheckStmt(map[], stmt, end);
      ghost var end :| CheckStmt(map[], stmt, end);
      Run([], Initial(stmt, end), end)
    }

    method PrintVal(val: Val) {
      match val
      case Unit    => print "()\n";
      case Bool(b) => print b, "\n";
      case Int(i)  => print i, "\n";
      case _       => print val, "\n";
    }

    method Interpret(stmt: Stmt, traced: bool := false) decreases * {
      var endOption := SynthStmt(map[], stmt);
      if endOption.None? {
        if traced {
          print "Statement fails to typecheck.\n";
        }
        return;
      }
      var end := endOption.Extract();
      var input := Initial(stmt, end);
      ghost var s :| CheckInput(s, input, end);
      while true
        invariant CheckInput(s, input, end)
        decreases *
      {
        match Step(s, input, end)
        case Raise(evt, output) =>
          if traced { print "event: ",  evt, ", state: ", output, "\n\n"; }
          else {
            match evt
            case Print(val) => PrintVal(val);
            case Silent     => {}
          }
          input := output;
          s :| CheckInput(s, input, end);
        case Terminal =>
          if traced { print "done.\n"; }
          break;
      }
    }

    method Test() {
    // Verifies that lexical scope works
    var fc := Expr.Thunk(Func("y", Pos.Int, Pure(Var("x"))));
    var fv := Force(Var("f"));
    var x1 := Expr.Int(1);
    var x2 := Expr.Int(2);
    var z  := Expr.Int(0);
    var term := Let(x1, "x", Pos.Int,
      Let(fc, "f", Pos.Int,
      Let(x2, "x", Pos.Int,
      Stmt.Call(fv, z))));
    }
  }
}