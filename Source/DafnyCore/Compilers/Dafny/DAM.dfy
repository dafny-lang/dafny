/* The Dafny Abstract Machine
 * This file specifies:
 * 1. A core language for Dafny based on call-by-push-value (CBPV)
 * 2. A novel CEK-machine interpreter (Levy's is a CK machine)
 * 3. Eventually, a simple type system based on CBPV
 * 4. Eventually, a type soundness result of the CEK-machine w.r.t. the type system
*/ 

datatype Option<A> = None | Some(value: A) {
    predicate IsFailure() { this.None? }
    function PropagateFailure(): Option<A>
        requires IsFailure() { None }
    function Extract(): A
        requires !IsFailure() { this.value }
}

class Ptr<A> {
  var deref: A
  constructor(expr: A) {
    deref := expr;
  }
}

datatype Expr =
// G, x : A+ |- x : A+
  Var(string)
// G |- true/false : Bool
| Bool(bool)
| Int(int)
// TODO: variant types
| Thunk(Stmt)
| Ref(Ptr<Val>)

// G |- e : D and D |- V : A+ ~> G |- V 
//type Heap = set<Ptr<Stmt>>

datatype Stmt =
// Intro & Elim for Up(A+)
  Pure(Expr)
| Bind(lhs: Stmt, var_: string, rhs: Stmt)
// Elim for bools
| Ite(guard: Expr, then_: Stmt, else_: Stmt)
// Intro & Elim for arrows
| Func(bound: string, body: Stmt)
| Call(func: Stmt, arg: Expr)
// Intro & Elim for objects/records
//| Object(record: map<string, Stmt>)
//| Select(object: Stmt, field: string)
// Elim for thunks
| Force(Expr)
// Elims for refs
| Read(ref: Expr, var_: string, cont: Stmt)
| Write(l: Expr, r: Expr, cont: Stmt)
{
    // TODO calculate Heap of a comp
}

// G |- (e, v) : A iff exists D. G |- e : D and D |- V : A
datatype Val =
  Bool(bool)
| Int(int)
| Thunk(Env, Stmt)
| Ref(Ptr<Val>)
// G |- e : D iff for all x : A in D, G |- e[x] : A
type Env = map<string, Val>

// 
datatype Frame =
  Bind(var_: string, rhs: Stmt)
| Call(arg: Expr)
//| Select(field: string)

datatype Stack = Empty | Push(top: Frame, rest: Stack) {
    function Pop(): Option<(Frame, Stack)> {
        match this
        case Empty      => None
        case Push(t, r) => Some((t, r))
    }
}

// CEK Machine
// In state = Computation, Environment, stacK
// (E, C, K) : B-   iff   E |- G  and  G |- C : A-  and  G |- K : A- << B-
type     In  = (Env, Stmt, Stack)
// TODO calculate Heap of In
datatype Out = Next(In) | Stuck | Terminal(Val)

function Eval(env: Env, expr: Expr): Val {
    match expr
    case Var(x) =>
        // Type soundness will discharge this assumption
        assume {:axiom} x in env;
        env[x]
    case Bool(b)  => Val.Bool(b)
    case Int(i)   => Val.Int(i)
    // The Felleisen-Friedman trick: delay
    // substitution by constructing a closure
    case Thunk(c) => Val.Thunk(env, c)
    case Ref(ptr) => Val.Ref(ptr)
}

// This function either steps the current state or tells you that it's terminal/stuck
// Type soundness = well-typed configs don't get stuck!
// TODO: replace * with Heap of state
// TODO: shouldn't stuck be auto-propagated?
function Step(state: In): Out reads * {
    var (env, comp, stack) := state;
    match comp
    case Bind(lhs, var_, rhs) =>
        Next((env, lhs, Push(Frame.Bind(var_, rhs), stack)))
    
    case Pure(expr) => (
        match stack.Pop()
        case Some((Bind(var_, rhs), stack)) =>
            Next((env[var_ := Eval(env, expr)], rhs, stack))
        
        case Some(_) => Stuck
        case None    => Terminal(Eval(env, expr))
    )

    case Call(func, arg) =>
        Next((env, func, Push(Frame.Call(arg), stack)))
    
    case Func(bound, body) => (
        match stack.Pop()
        case Some((Call(arg), stack)) =>
            Next((env[bound := Eval(env, arg)], body, stack))
        
        case Some(_) => Stuck
        case None    => Terminal(Val.Thunk(env, comp))
    )

    case Ite(guard, then_, else_) => (
        match Eval(env, guard)
        case Bool(guard) =>
            Next((env, if guard then then_ else else_, stack))
        
        case _ => Stuck
    )

    // Lexical scope restores the env of the closure
    case Force(thunk) => (
        match Eval(env, thunk)
        case Thunk(env, c) => Next((env, c, stack))
        
        case _        => Stuck
    )
    
    case Read(ref, var_, cont) => (
        match Eval(env, ref)
        case Ref(ptr) => Next((env[var_ := ptr.deref], cont, stack))
        case _        => Stuck
    )

    case Write(lhs, rhs, cont) => (
        match Eval(env, lhs)
        case Ref(ptr) =>
            (/*ptr.deref := Eval(env, rhs);*/ Next((env, cont, stack)))
        case _        => Stuck
    )
}

// Iterates step
method Run(s: In) decreases * {
    print("\n");
    match Step(s)
    case Next(s) => print(s, "\n"); Run(s);
    case _ => print "done/stuck\n"; return;
}

// Initial configuration
function Initial(comp: Stmt): In
    { (map[], comp, Empty) }

function Let(lhs: Expr, var_ : string, rhs: Stmt): Stmt
    { Stmt.Call(Func(var_, rhs), lhs) }

method Main() decreases * {
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
    var fc := Expr.Thunk(Func("y", Pure(Var("x"))));
    var fv := Force(Var("f"));
    var x1 := Expr.Int(1);
    var x2 := Expr.Int(2);
    var z  := Expr.Int(0);
    Run(Initial(
        Let(x1, "x",
        Let(fc, "f",
        Let(x2, "x",
        Stmt.Call(fv, z))))
    ));
}

