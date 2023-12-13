/* The Dafny Abstract Machine
 * This file specifies:
 * 1. A core language for Dafny based on call-by-push-value (CBPV) with
 *    state (mutable references), control (letcc/throw) for early returns, etc., and recursion 
 * 2. A novel CEK-machine interpreter that extends the CK machine for CBPV
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
  }

  module Machine {
    import opened Syntax
    import opened Utils

    // The environment accumulates substitutions made along the course of machine execution, i.e.,
    // maps variables to addresses of values - closed intro. forms of positive type
    type Ptr = nat    
    type Env = Alist<Var, Ptr>
    type Store = seq<Val>

    predicate Allocated(sto: Store, ptr: Ptr) {
      ptr < |sto|
    }

    function Alloc(env: Env, sto: Store, var_: Var, val: Val): (Env, Store) {
      (Update(var_, |sto|, env), sto + [val])
    }

    function Deref(env: Env, sto: Store, var_: Var): Option<Val> {
      var ptr :- Get(env, var_);
      if Allocated(sto, ptr) then
        Some(sto[ptr])
      else
        None
    }

    // To implement lexical scope, thunks and stacks are closures that save the environment they're defined in
    datatype Val =
      Unit
    | Bool(bool)
    | Int(int)
    | Thunk(Env, Stmt)
    | Ref(Ptr)
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
    | Select(field: Field)

    // States of the CESK Machine
    type     In  = (Env, Store, Stmt, Stack)
    datatype Out = Next(In) | Stuck | Terminal
  }

  module Statics {
    import opened Utils
    import opened Syntax
    import opened Machine

    type Context = Alist<Var, Pos>

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

    predicate CheckExpr(g: Context, e: Expr, t: Pos) decreases e, 1 {
      SynthExpr(g, e) == Some(t)
    }

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

    predicate CheckStmt(g: Context, s: Stmt, t: Neg) decreases s, 1 {
      SynthStmt(g, s) == Some(t)
    }

    function SynthStack(g: Context, stack: Stack, start: Neg): Option<Neg> decreases stack {
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

    predicate CheckStack(g: Context, stack: Stack, start: Neg, end: Neg) {
      SynthStack(g, stack, start) == Some(end)
    }

    lemma SynthStackWeakening(g: Context, stack: Stack, start: Neg, var_: Var, t: Pos)
    ensures SynthStack(Update(var_, t, g), stack, start) == SynthStack(g, stack, start)

    type StoreTyping = seq<Pos>

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
      case Ref(ptr) => if ptr < |s| then Some(s[ptr]) else None
      /*case Stack(env, stack) => (
        var g :- SynthEnv(s, env);
        var end :- SynthStack(g, stack, start);
        Some(Pos.Stack(end))
      )*/
      case _ => None
    }

    predicate CheckVal(s: StoreTyping, val: Val, t: Pos) {
      SynthVal(s, val) == Some(t)
    }

    function SynthEnv(s: StoreTyping, env: Env): Option<Context> decreases env
    {
      match env
      case Empty             => Some(Alist.Empty)
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

    function SynthIn(s: StoreTyping, input: In): Option<Neg> {
      var (env, sto, stmt, stack) := input;
      var g :- SynthEnv(s, env);
      var start :- SynthStmt(g, stmt);
      var end :- SynthStack(g, stack, start);
      Some(end)
    }

    predicate CheckIn(s: StoreTyping, input: In, end: Neg) {
      SynthIn(s, input) == Some(end)
    }

    predicate EvalPreservation(s: StoreTyping, env: Env, e: Expr, v: Val) {
      match SynthEnv(s, env)
      case Some(g) => (
        match SynthExpr(g, e)
        case Some(t) => CheckVal(s, v, t)
        // Assuming the expression is well-typed
        case None    => true
      )
      // Assuming the environment is well-typed
      case None    => true
    }

    predicate StepPreservation(s: StoreTyping, input: In, output: Out) {
      match SynthIn(s, input)
      case Some(end) => (
        match output
        case Next(next) => CheckIn(s, next, end)
        // Assumes a step was made at all
        case Stuck      => true
        case Terminal   => true
      )
      // Assumes the input state is well-typed
      case None => true
    }
  }

  module Dynamics {
    import opened Utils
    import opened Syntax
    import opened Machine
    import opened Statics

    

    // Small-step semantics are divided between evaluation of expressions and stepping of the machine
    function Eval(env: Env, sto: Store, expr: Expr): (out: Option<Val>)
      ensures (match out
        case Some(val) => forall s :: EvalPreservation(s, env, expr, val)
        case None      => true)
    {
      match expr
      case Var(x)      => (
        assume false;
        Deref(env, sto, x)
      )
      case Unit        => Some(Val.Unit)
      case Bool(b)     => Some(Val.Bool(b))
      case Int(i)      => Some(Val.Int(i))
      case Thunk(stmt) => Some(Val.Thunk(env, stmt))
    }

    function Step(input: In, ghost end: Neg): (output: Out)

      ensures forall s : StoreTyping :: StepPreservation(s, input, output)
    {
      var (env, sto, stmt, stack) := input;
      match stmt
      case Bind(lhs, var_, rhs) =>
        Next((env, sto, lhs, Push(Frame.Bind(var_, rhs), stack)))
      
      /*case Pure(expr) => {
        match stack.Pop()
        case Some((Bind(var_, rhs), stack')) => {
          match Eval(env, expr)
          case Some(val) =>*/

      /*case Ite(guard, then_, else_) => {
        var val := Eval(env, guard);
        match val
        case Some(Bool(answer)) =>
          var val := Val.Bool(answer);
          out := Next((env, if answer then then_ else else_, stack));

          // Proof of preservation
          forall s : Store ensures StepPreservation(s, state, out) {
            match SynthEnv(s, env)
            case None => {}
            case Some(g) => {
              match SynthStmt(g, comp)
              case None => {}
              case Some(start) => {
                match SynthStack(g, stack, start)
                case None => {}
                case Some(end) => {
                  assert CheckExpr(g, guard, Pos.Bool);
                  assert EvalPreservation(s, env, guard, val);
                  assert CheckVal(s, val, Pos.Bool);
                  
                  match SynthStmt(g, then_)
                  case None => {}
                  case Some(start) => {
                    assert CheckStmt(g, else_, start);
                    assert CheckStack(g, stack, start, end);
                  }
                }
              }
            }
          }

          return;
        case Some(_) => return Stuck;
        case None => return Stuck;
      }
      
      case Pure(expr) => {
        match stack.Pop()
        case Some((Bind(var_, rhs), stack')) => {
          var val := Eval(env, expr);
          match val
          case Some(val) =>
            var env' := Update(var_, val, env);
            out := Next((env', rhs, stack'));
            // Proof of preservation
            forall s : Store ensures StepPreservation(s, state, out) {
              match SynthEnv(s, env)
              case None => {}
              case Some(g) => {
                match SynthStmt(g, comp)
                case None => {}
                case Some(start) => {
                  match SynthStack(g, stack, start)
                  case None => {}
                  case Some(end) => {
                    match SynthExpr(g, expr)
                    case None => {}
                    case Some(t) => {
                    
                      assert EvalPreservation(s, env, expr, val);
                      assert CheckVal(s, val, t);
                      var g' := Update(var_, t, g);
                      assert CheckEnv(s, env', g');
                      
                      match SynthStmt(g', rhs)
                      case None => {}
                      case Some(start) => {
                        SynthStackWeakening(g, stack', start, var_, t);
                        assert CheckStack(g', stack', start, end);
                      }
                    }
                  }
                }
              }
            }
            return;
          case None      => return Stuck;
        }
        case Some(_) => return Stuck;
        case None    => return Terminal;
      }

      case Call(func, arg) =>
        return Next((env, func, Push(Frame.Call(arg), stack)));
      
      case Func(bound, _, body) => {
        match stack.Pop()
        case Some((Call(arg), stack')) => {
          var val := Eval(env, arg);
          match val
          case Some(val) =>
            var env' := Update(bound, val, env);
            out := Next((env', body, stack'));
            // Proof of preservation
            forall s : Store ensures StepPreservation(s, state, out) {
              // Assume that the old environment, statement, and stack are well-typed
              match SynthEnv(s, env)
              case None => {}
              case Some(g) => {
                match SynthStmt(g, comp)
                case None => {}
                case Some(start) => {
                  match SynthStack(g, stack, start)
                  case None => {}
                  case Some(end) => {
                    // Inversion on the function's type
                    match start
                    case Function(dom, cod) => {
                      assert CheckExpr(g, arg, dom);
                      assert EvalPreservation(s, env, arg, val);
                      assert CheckVal(s, val, dom);
                      var g' := Update(bound, dom, g);
                      assert CheckEnv(s, env', g');
                      assert CheckStmt(g', body, cod);
                      SynthStackWeakening(g, stack', cod, bound, dom);
                      assert CheckStack(g', stack', cod, end);
                    }
                    case _ => {}
                  }
                }
              }
            }
            return;
          case None      => return Stuck;
        }
        case Some(_) => return Stuck;
        case None    => return Terminal;
      }

      case Select(obj, field) =>
        return Next((env, obj, Push(Frame.Select(field), stack)));
      
      case Record(fields) => {
        match stack.Pop()
        case Some((Select(lbl), stack')) => {
          match Get(fields, lbl)
          case Some(field) =>
            out := Next((env, field, stack'));
            forall s : Store ensures StepPreservation(s, state, out) {
              match SynthEnv(s, env)
              case None => {}
              case Some(g) => {
                match SynthStmt(g, comp)
                case None => {}
                case Some(start) => {
                  match SynthStack(g, stack, start)
                  case None => {}
                  case Some(end) => {
                    match start
                    case Record(fieldts) => {
                      match Get(fieldts, lbl)
                      case None => {}
                      case Some(fieldt) =>
                        assert CheckEnv(s, env, g);
                        assume CheckStmt(g, field, fieldt);
                        assert CheckStack(g, stack', fieldt, end);
                    }
                    case _ => {}
                  }
                }
              }
            }
            return;
          case None        => return Stuck;
        }
        case Some(_) => return Stuck;
        case None    => return Terminal;
      }

      // Lexical scope restores the env of the closure
      case Force(thunk) => {
        var val := Eval(env, thunk);
        match val
        case Some(Thunk(env', stmt)) =>
          out := Next((env', stmt, stack));
          forall s : Store ensures StepPreservation(s, state, out) {
            match SynthEnv(s, env)
            case None => {}
            case Some(g) => {
              match SynthStmt(g, comp)
              case None => {}
              case Some(start) => {
                match SynthStack(g, stack, start)
                case None => {}
                case Some(end) => {
                  match SynthExpr(g, thunk)
                  case Some(Thunk(t)) => {
                    assert EvalPreservation(s, env, thunk, val.value);
                    assert CheckVal(s, val.value, Pos.Thunk(t));
                    // Context of env' is smaller than g
                    match SynthEnv(s, env')
                    case None => {}
                    case Some(g') => {
                      assume CheckStack(g', stack, start, end);
                    }
                  }
                  case Some(_) => {}
                  case None    => {}
                }
              }
            }
          }
        case _                      => return Stuck;
      }*/

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

      case Print(expr, next) => {
        match Eval(env, expr)
        case Some(val) =>
          print val, "\n";
          return Next((env, next, stack));
        case None => return Stuck;
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
      case _ => Terminal
    }

    //codatatype Trace = Step(In, Trace) | Stuck | Terminal
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
      { (Alist.Empty, [], comp, Stack.Empty) }
  }

  module Progress {
    import opened Utils
    import opened Syntax
    import opened Machine
    import opened Statics
    import opened Dynamics

    // Prove progress separately so we can do one big induction on the machine configuration


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