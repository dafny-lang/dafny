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

    datatype Alist<K, V> =
      Update(key: K, val: V, rest: Alist<K, V>)
    | Empty

    function Get<K(==), V>(alist: Alist<K, V>, key: K): Option<V> decreases alist {
      match alist
      case Empty  => None
      case Update(key', val, rest) =>
        if key == key' then
          Some(val)
        else
          Get(rest, key)
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
    | Ref(pos: Pos)
    | Stack(start: Neg)

    datatype Neg =
      Value(pos: Pos)
    | Function(dom: Pos, cod: Neg)
    // Alist instead of map so we can do induction on the set of fields for type synthesis
    | Record(fields: Alist<Field, Neg>)

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
    | Record(fields: Alist<Field, Stmt>)
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

    // The environment accumulates substitutions made along the course of machine execution, i.e.,
    // maps variables to addresses
    
    // The store maps addresses to values - closed intro. forms of positive type

    type Ptr = nat

    // Alist instead of map so we can do induction on envs for type synthesis
    type Env = Alist<Var, Ptr>

    type Store = seq<Val>

    predicate Allocated(sto: Store, ptr: Ptr) {
      ptr < |sto|
    }

    type ClosedExpr = (Env, Expr)

    type ClosedStmt = (Env, Stmt)

    // To implement lexical scope, thunks and stacks are closures that save the environment they're defined in
    datatype Val =
      Unit
    | Bool(answer: bool)
    | Int(int)
    | Thunk(closure: ClosedStmt)
    | Ref(ptr: Ptr)
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
    type     In  = (Store, ClosedStmt, Stack)
    datatype Out = Next(In) | Terminal
  }

  module Statics {
    import opened Utils
    import opened Syntax
    import opened Machine

    // Honestly, I forgot why this is an alist
    type Context = Alist<Var, Pos>

    // G |- expr => t+
    function SynthExpr(g: Context, expr: Expr): Option<Pos> decreases expr, 0 {
      match expr
      case Var(x)   => Get(g, x)
      case Unit     => Some(Pos.Unit)
      case Bool(_)  => Some(Pos.Bool)
      case Int(_)   => Some(Pos.Int)
      case Thunk(s) => (
        var t :- SynthStmt(g, s);
        Some(Pos.Thunk(t))
      )
    }

    // G |- expr <= t+
    predicate CheckExpr(g: Context, e: Expr, t: Pos) decreases e, 1 {
      SynthExpr(g, e) == Some(t)
    }

    // G |- stmt => t-
    function SynthStmt(g: Context, stmt: Stmt): Option<Neg> decreases stmt, 0 {
      match stmt
      case Pure(e) => (
        var t :- SynthExpr(g, e);
        Some(Neg.Value(t))
      )

      case Bind(lhs, var_, rhs) => (
        match SynthStmt(g, lhs)
        case Some(Value(t)) => SynthStmt(Update(var_, t, g), rhs)
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
        var cod :- SynthStmt(Update(bound, dom, g), body);
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
        var fields :- SynthRecord(g, fields);
        Some(Neg.Record(fields))
      )

      case Select(record, field) => (
        match SynthStmt(g, record)
        case Some(Record(fields)) => (
          match Get(fields, field)
          case Some(field) => Some(field)
          case None        => None
        )
        case _ => None
      )

      case New(init, var_, next) =>
        var t :- SynthExpr(g, init);
        SynthStmt(Update(var_, Pos.Ref(t), g), next)

      case Read(ref, var_, next) => (
        match SynthExpr(g, ref)
        case Some(Ref(t)) => SynthStmt(Update(var_, t, g), next)
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

    function SynthRecord(g: Context, fields: Alist<Field, Stmt>): Option<Alist<Field, Neg>> decreases fields {
      match fields
      case Empty => Some(Alist.Empty)
      case Update(field, stmt, rest) =>
        var fieldt :- SynthStmt(g, stmt);
        var rest  :- SynthRecord(g, rest);
        Some(Update(field, fieldt, rest))
    }

    // G |- stmt <= t-
    predicate CheckStmt(g: Context, stmt: Stmt, t: Neg) decreases stmt, 1 {
      SynthStmt(g, stmt) == Some(t)
    }

    // start- => stack => end-
    function SynthStack(stack: Stack, start: Neg): Option<Neg> decreases stack {
      match stack
      case Empty => Some(start)
      case Push(Bind(var_, rhs), stack) => (
        match start
        case Value(t) => (
          match SynthStmt(Update(var_, t, g), rhs)
          case Some(start) => SynthStack(g, stack, start)
          case None        => None
        )
        case _        => None
      )

      case Push(Select(field), stack) => (
        match start
        case Record(fields) =>
          var field :- Get(fields, field);
          SynthStack(g, stack, field)
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

    // G |- stack <= start- <= end-
    predicate CheckStack(g: Context, stack: Stack, start: Neg, end: Neg) {
      SynthStack(g, stack, start) == Some(end)
    }

    lemma SynthStackWeakening(g: Context, stack: Stack, start: Neg, var_: Var, t: Pos)
    ensures SynthStack(Update(var_, t, g), stack, start) == SynthStack(g, stack, start)

    type StoreTyping = seq<Pos>

    // S |- val => t+
    function SynthVal(s: StoreTyping, val: Val): Option<Pos> decreases val {
      match val
      case Unit        => Some(Pos.Unit)
      case Bool(_)     => Some(Pos.Bool)
      case Int(_)      => Some(Pos.Int)
      case Thunk(env, stmt) => (
        var g :- SynthEnv(s, env);
        var t :- SynthStmt(g, stmt);
        Some(Pos.Thunk(t))
      )
      case Ref(ptr) => if ptr < |s| then Some(Pos.Ref(s[ptr])) else None
      /*case Stack(env, stack) => (
        var g :- SynthEnv(s, env);
        var end :- SynthStack(g, stack, start);
        Some(Pos.Stack(end))
      )*/
      case _ => None
    }

    // S |- val <= t+
    predicate CheckVal(s: StoreTyping, val: Val, t: Pos) {
      SynthVal(s, val) == Some(t)
    }

    function SynthEnv(s: StoreTyping, env: Env): Option<Context> decreases env {
      match env
      case Empty => Some(Alist.Empty)
      case Update(var_, ptr, env) =>
        if ptr < |s| then
          var rest :- SynthEnv(s, env);
          Some(Update(var_, s[ptr], rest))
        else
          None
    }

    // Sleight of hand: assumes synthesis produces context in the same order as g
    predicate CheckEnv(s: StoreTyping, env: Env, g: Context) {
      SynthEnv(s, env) == Some(g)
    }

    lemma CheckEnvInduction(s: StoreTyping, env: Env, g: Context, var_: Var, t: Pos)
      requires CheckEnv(s, env, g)
      ensures CheckEnv(s + [t], Update(var_, |s| + 1, env), Update(var_, t, g))
    
    // sto |- S
    predicate {:induction sto} CheckStore(s: StoreTyping, sto: Store) {
      forall ptr | 0 <= ptr < |sto| :: ptr < |s| && CheckVal(s, sto[ptr], s[ptr])
    }

    lemma CheckStoreInduction(s: StoreTyping, sto: Store, val: Val, t: Pos)
      requires CheckStore(s, sto)
      requires CheckVal(s, val, t)
      ensures  CheckStore(s + [t], sto + [val])

    // S |- input => end
    function SynthIn(s: StoreTyping, input: In): Option<Neg> {
      var (env, sto, stmt, stack) := input;
      if CheckStore(s, sto) then
        var g :- SynthEnv(s, env);
        var start :- SynthStmt(g, stmt);
        var end :- SynthStack(g, stack, start);
        Some(end)
      else
        None
    }

    // S |- input <= end
    predicate CheckIn(s: StoreTyping, input: In, end: Neg) {
      SynthIn(s, input) == Some(end)
    }

    predicate CheckOut(s: StoreTyping, out: Out, end: Neg) {
      match out
      case Next(next) => CheckIn(s, next, end)
      case Terminal   => true
    }
  }

  module Dynamics {
    import opened Utils
    import opened Syntax
    import opened Machine
    import opened Statics

    // Well-typed reference allocation and initialization
    function Alloc(ghost s: StoreTyping, sto: Store, env: Env, ghost g: Context, var_: Var, val: Val, ghost t: Pos): (out: (Env, Store))
      requires CheckStore(s, sto)
      requires CheckEnv(s, env, g)
      requires CheckVal(s, val, t)
      ensures
        var s' := s + [t];
        var g' := Update(var_, t, env);
        && CheckStore(s', out.1)
        && CheckEnv(s', out.0, g')
    {
      (Update(var_, |sto|, env), sto + [val])
    }

    // Big-step evaluation of expressions
    function Eval(ghost s: StoreTyping, sto: Store, env: Env, ghost g: Context, expr: Expr, ghost t: Pos): (out: Val)
      requires CheckStore(s, sto)    // sto |- S
      requires CheckEnv(s, env, g)   // S |- env <= G
      requires CheckExpr(g, expr, t) // G |- expr <= t
      ensures  CheckVal(s, out, t)   // S |- out  <= t
    {
      // Proof by inversion on t
      match expr
      case Var(x)      => (
        assume Get(env, x).Some?;
        assume Get(env, x).value < |sto|;
        assume CheckVal(s, sto[Get(env, x).Extract()], t);
        sto[Get(env, x).Extract()]
      )
      case Unit        =>
        assert CheckExpr(s, expr, Pos.Unit);
        Val.Unit
      case Bool(b)     =>
        assert CheckExpr(g, expr, Pos.Bool);
        Val.Bool(b)
      case Int(i)      =>
        assert CheckExpr(g, expr, Pos.Int);
        Val.Int(i)
      case Thunk(stmt) =>
        assume CheckVal(s, Val.Thunk(env, stmt), t);
        Val.Thunk(env, stmt)
    }

    // Type-preserving small-step reduction for the CESK machine
    // Progress = totality, preservation = requires + ensures clause
    function Step(ghost s: StoreTyping, input: In, ghost end: Neg): (output: Out)
      requires CheckIn(s, input, end)
      // s <= s' b/c no deallocations occur...for now!
      ensures  exists s' | s <= s' :: CheckOut(s', output, end)
    {
      var (env, sto, stmt, stack) := input;

      assert CheckStore(s, sto);
      ghost var g     := SynthEnv(s, env).Extract();
      ghost var start := SynthStmt(g, stmt).Extract();
      ghost var end   := SynthStack(g, stack, start).Extract();

      match stmt
      case Bind(lhs, var_, rhs) =>
        var output := Next((env, sto, lhs, Push(Frame.Bind(var_, rhs), stack)));
        assert CheckOut(s, output, end);
        output
      
      case Pure(expr) => (
        match stack.Pop()
        case Some((Bind(var_, rhs), stack')) => (
          ghost var t := start.pos;

          var val := Eval(s, sto, env, g, expr, t);

          ghost var s' := s + [t];
          ghost var g' := Update(var_, t, g);
          var (env', sto') := Alloc(env, sto, var_, val);

          CheckStoreInduction(s, sto, val, t);
          CheckEnvInduction(s, env, g, var_, t);
          var start' := SynthStmt(g', rhs).Extract();
          SynthStackWeakening(g, stack', start', var_, t);

          var output := Next((env', sto', rhs, stack'));
          assert CheckOut(s', output, end);
          output
        )
        case None =>
          var output := Terminal;
          assert CheckOut(s, output, end);
          output
      )

      case Call(func, arg) =>
        var output := Next((env, sto, func, Push(Frame.Call(arg), stack)));
        assert CheckOut(s, output, end);
        output
      
      case Func(bound, _, body) => (
        match stack.Pop()
        case Some((Call(arg), stack')) =>
          ghost var dom := start.dom;
          ghost var cod := start.cod;

          var val := Eval(s, sto, env, g, arg, dom);

          ghost var g' := Update(bound, dom, g);
          ghost var s' := s + [dom];
          var (env', sto') := Alloc(env, sto, bound, val);
          
          CheckStoreInduction(s, sto, val, dom);
          CheckEnvInduction(s, env, g, bound, dom);
          assert CheckStmt(g', body, cod);
          SynthStackWeakening(g, stack', cod, bound, dom);

          var output := Next((env', sto', body, stack'));
          assert CheckOut(s', output, end);
          output
        
        case None =>
          var output := Terminal;
          assert CheckOut(s, output, end);
          output
      )

      case Select(record, field) =>
        var output := Next((env, sto, record, Push(Frame.Select(field), stack)));
        assert CheckOut(s, output, end);
        output
      
      case Record(fields) => (
        match stack.Pop()
        case Some((Select(lbl), stack')) => (
          var fieldt := Get(SynthRecord(g, fields).Extract(), lbl).Extract();
          assume Get(fields, lbl).Some?;
          var field := Get(fields, lbl).Extract();
          var output := Next((env, sto, field, stack'));
          assume CheckStmt(g, field, fieldt);
          assert CheckOut(s, output, end);
          output
        )

        case None =>
          var output := Terminal;
          assert CheckOut(s, output, end);
          output
      )
      
      case Ite(guard, then_, else_) => (
        var val := Eval(s, sto, env, g, guard, Pos.Bool);
        var output := Next((env, sto, if val.answer then then_ else else_, stack));
        assert CheckOut(s, output, end);
        output
      )

      case Print(expr, next) => (
        ghost var t := SynthExpr(g, expr).Extract();
        var val := Eval(s, sto, env, g, expr, t);
        //print val, "\n";
        var output := Next((env, sto, next, stack));
        assert CheckOut(s, output, end);
        output
      )

      /*
      // Lexical scope restores the env of the closure
      case Force(thunk) => {
        var closure := Eval(env, thunk);
        out := Next((closure.env, closure.stmt, stack));
      }*/

      case _ =>
        var output := Terminal;
        assert CheckOut(s, output, end);
        output
      
      /*
      case New(init, var_, next) => {
        match Eval(env, init)
        case Some(init) =>
          var ptr := new Ptr(init);
          return Next((Update(var_, Val.Ref(ptr), env), next, stack));
        case None => return Stuck;
      }

      case Read(ref, var_, next) => {
        match Eval(env, ref)
        case Some(Ref(ptr)) => return Next((Update(var_, ptr.deref, env), next, stack));
        case _              => return Stuck;
      }

      case Write(lval, rval, next) => {
        match Eval(env, lval)
        case Some(Ref(ptr)) =>
          //ptr.deref := Eval(env, rval);
          return Next((env, next, stack));
        case _        => return Stuck;
      }

      
      
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
    /*codatatype Trace = Stepping(In, Trace) | Done

    function Run(ghost s: StoreTyping, input: In, ghost end: Neg): Trace
      requires CheckIn(s, input, end)
    {
      match Step(s, input, end)
      case Next(next) => Stepping(next, Run(s, next, end))
      case Terminal   => Done
    }*/

    // Initial configuration
    function Initial(comp: Stmt): In
      { (Alist.Empty, [], comp, Stack.Empty) }
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