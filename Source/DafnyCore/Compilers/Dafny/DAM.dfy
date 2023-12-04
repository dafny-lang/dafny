/* The Dafny Abstract Machine
 * This file specifies:
 * 1. A core language for Dafny based on call-by-push-value (CBPV)
 * 2. A novel CEK-machine interpreter (Levy's is a CK machine)
 * 3. Eventually, a simple type system based on CBPV
 * 4. Eventually, a type soundness result of the CEK-machine w.r.t. the type system
*/ 

module {:extern "DAM"} DAM {

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

type Var = string
type Field = string

//module Typing {
datatype Pos =
  Unit
| Bool
| Int
| Thunk(Neg)
| Ref(Pos)
| Stack(Neg)

datatype Neg =
  Value(Pos)
| Function(dom: Pos, cod: Neg)
| Record(fields: map<Field, Neg>)

type Context = map<Var, Pos>

// Hamza-Voirol-Kuncak trick: annotate terms just enough so that ostensible checking terms synthesize

function SynthPos(g: Context, e: Expr): Option<Pos> {
    match e
    case Var(x)   => if x in g then Some(g[x]) else None
    case Unit     => Some(Pos.Unit)
    case Bool(_)  => Some(Pos.Bool)
    case Int(_)   => Some(Pos.Int)
    case Thunk(s) => (
        match SynthNeg(g, s)
        case Some(t) => Some(Pos.Thunk(t))
        case _       => None
    )
    case Ref(p)   => Some(Pos.Int)
}

predicate CheckPos(g: Context, e: Expr, t: Pos) {
    SynthPos(g, e) == Some(t)
}

predicate CheckNeg(g: Context, s: Stmt, t: Neg) {
    SynthNeg(g, s) == Some(t)
}

function SynthNeg(g: Context, s: Stmt): Option<Neg> decreases s {
    match s
    case Pure(e) => (
        match SynthPos(g, e)
        case Some(t) => Some(Neg.Value(t))
        case _       => None
    )
    
    case Bind(lhs, var_, rhs) => (
        match SynthNeg(g, lhs)
        case Some(Value(t)) => SynthNeg(g[var_ := t], rhs)
        case _              => None
    )
    
    /*case Ite(guard, then_, else_) => (
        :- CheckPos(guard, Pos.Bool);
        var t :- SynthNeg(g, then_, t);
        if CheckNeg(g, else_, t) then Some(t) else None
    )*/

    case Func(bound, dom, body) => (
        var cod :- SynthNeg(g[bound := dom], body);
        Some(Function(dom, cod))
    )

    case Call(func, arg) => (
        match SynthNeg(g, func)
        case Some(Function(dom, cod)) => (
            if CheckPos(g, arg, dom) then Some(cod) else None
        )
        case _ => None
    )
    
    case Force(expr) => (
        match SynthPos(g, expr)
        case Some(Thunk(t)) => Some(t)
        case _              => None
    )

    case Print(expr, next) => (
        match SynthPos(g, expr)
        case Some(_) => SynthNeg(g, next)
        case _       => None
    )

    /*case Record(fields) => (
        for i := 0 to  {
            match SynthNeg(g, fields[i])
            case Some() => 
            case None   => return None;
        }
    )*/

    case Select(record, field) => (
        match SynthNeg(g, record)
        case Some(Record(fields)) =>
            if field in fields then Some(fields[field]) else None
        case _ => None
    )

    case _ => None
}

//}

datatype Expr =
// G, x : A+ |- x : A+
  Var(Var)
| Unit
// G |- true/false : Bool
| Bool(bool)
| Int(int) 
// TODO: variant types
| Thunk(Stmt)
| Ref(Ptr<Val>)

//type Heap = set<Ptr<Stmt>>

datatype Stmt =
// Intro & Elim for expressions
  Pure(Expr)
| Bind(lhs: Stmt, var_: Var, rhs: Stmt)
// Elim for bools
| Ite(guard: Expr, then_: Stmt, else_: Stmt)
// Intro & Elim for arrows
| Func(bound: Var, dom: Pos, body: Stmt)
| Call(func: Stmt, arg: Expr)
// Intro & Elim for objects/records
| Record(fields: map<string, Stmt>)
| Select(record: Stmt, field: Field)
// Elim for thunks
| Force(Expr)
// Elims for refs
| Read(ref: Expr, var_: Var, cont: Stmt)
| Write(lvalue: Expr, rvalue: Expr, next: Stmt)
// Print
| Print(Expr, next: Stmt)
// Recursion
| Rec(bound: Var, body: Stmt)
// Let-current-stack (letcc, basically) and throw
| LetCS(bound: Var, body: Stmt)
| Throw(stack: Expr, init: Stmt)
{
    // TODO calculate Heap of a comp
}

// Let-bindings
function Let(lhs: Expr, var_ : string, ty: Pos, rhs: Stmt): Stmt
    { Stmt.Call(Func(var_, ty, rhs), lhs) }

/** Guarded commands / imperative substrate of Dafny */
function Then(lhs: Stmt, rhs: Stmt): Stmt
    { Stmt.Bind(lhs, "_", rhs) }

function Skip(): Stmt
    { Pure(Expr.Unit) }

function While(guard: Stmt, body: Stmt, next: Stmt): Stmt {
    Rec("while", Stmt.Bind(guard, "if",
        Ite(Var("if"), Then(body, Force(Var("while"))), next)))
}

// G |- (e, v) : A iff exists D. G |- e : D and D |- V : A
datatype Val =
  Unit
| Bool(bool)
| Int(int)
| Thunk(Env, Stmt)
| Ref(Ptr<Val>)
| Stack(Env, Stack)

// G |- e : D iff for all x : A in D, G |- e[x] : A
type Env = map<string, Val>

// Stack frames (one for each negative type elimination)
datatype Frame =
  Bind(var_: Var, rhs: Stmt)
| Call(arg: Expr)
| Select(field: string)

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
    case Unit     => Val.Unit
    case Bool(b)  => Val.Bool(b)
    case Int(i)   => Val.Int(i)
    // The Felleisen-Friedman trick: delay
    // substitution by constructing a closure
    case Thunk(c) => Val.Thunk(env, c)
    case Ref(ptr) => Val.Ref(ptr)
}

// Small-step semantics
// Type soundness = well-typed configs don't get stuck!
// TODO: replace * with Heap of state
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
    
    case Func(bound, _, body) => (
        match stack.Pop()
        case Some((Call(arg), stack)) =>
            Next((env[bound := Eval(env, arg)], body, stack))
        
        case Some(_) => Stuck
        case None    => Terminal(Val.Thunk(env, comp))
    )

    case Select(obj, field) =>
        Next((env, obj, Push(Frame.Select(field), stack)))
    
    case Record(fields) => (
        match stack.Pop()
        case Some((Select(field), stack)) =>
            if field in fields then
                Next((env, fields[field], stack))
            else
                Stuck
        
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
        case Thunk(env, comp) => Next((env, comp, stack))
        case _             => Stuck
    )
    
    case Read(ref, var_, cont) => (
        match Eval(env, ref)
        case Ref(ptr) => Next((env[var_ := ptr.deref], cont, stack))
        case _        => Stuck
    )

    case Write(lval, rval, next) => (
        match Eval(env, lval)
        case Ref(ptr) =>
            (/*ptr.deref := Eval(env, rval);*/ Next((env, next, stack)))
        case _        => Stuck
    )

    case Print(expr, next) =>
        (/*print Eval(env, expr), "\n";*/ Next((env, next, stack)))

    case Rec(self, body) =>
        Next((env[self := Val.Thunk(env, comp)], body, stack))

    case LetCS(bound, body) =>
        Next((env[bound := Val.Stack(env, stack)], body, stack))
    
    case Throw(stack, init) => (
        match Eval(env, stack)
        case Stack(env, stack) => Next((env, init, stack))
        case _                 => Stuck
    )
}

//codatatype Trace = Next(In, Trace) | Stuck | Terminal(Val)

// Big-step semantics coinductively iterates the small-step
method Run(s: In) decreases * {
    print("\n");
    match Step(s)
    case Next(s) => print(s, "\n"); Run(s);
    case _ => print "done/stuck\n"; return;
}

// Initial configuration
function Initial(comp: Stmt): In
    { (map[], comp, Empty) }

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
}

}