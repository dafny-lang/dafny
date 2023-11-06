/* The Dafny Abstract Machine
 * This file specifies:
 * 1. A core language for Dafny based on Levy's fine-grain call-by-value (FG-CBV) calculus
 * 2. A CEK-machine interpreter that extends Levy's CK-machine with environments (substitution model is bad for named variables)
 * 3. Eventually, a simple type system based on Levy's call-by-push-value (CBPV) to account for reference types (FG-CBV only has value types)
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
  constructor(val: A) {
    deref := val;
  }
}

datatype Val =
// G, x : A+ |- x : A+
  Var(string)
// G |- true/false : Bool
| Bool(bool)
| Int(int)
// TODO: datatypes
// G |- Ref(new Ptr(C)) : Ref(A-) if G |- C : A-
| New(Ptr<Comp>) // comps have to be terminal like in FG-CBV / unlike CBPV

datatype Obj = FuncC(string, Comp) | Record(map<string, Comp>)

// G |- e : D and D |- V : A+ ~> G |- V 
//type Heap = set<Ptr<Comp>>

datatype Comp =
// Intro & Elim for Up(A+)
  Pure(Val)
| Bind(lhs: Comp, var_: string, rhs: Comp)
// Elim for bools
| Ite(guard: Val, then_: Comp, else_: Comp)
// Intro & Elim for arrows
| Func(bound: string, body: Comp)
| Call(func: Comp, arg: Val)
// Intro & Elim for objects/records
//| Object(record: map<string, Comp>)
//| Select(object: Comp, field: string)
// Elims for refs (instead of Levy's Force)
| Read(ref: Val)
//| Write(lhs: Obj, ref: Val, rhs: Comp)
{
    // TODO calculate Heap of a comp
}
datatype Frame =
  Bind(var_: string, rhs: Comp)
| Call(arg: Val)
//| Select(field: string)

datatype Stack = Empty | Push(top: Frame, rest: Stack) {
    function Pop(): Option<(Frame, Stack)> {
        match this
        case Empty      => None
        case Push(t, r) => Some((t, r))
    }
}

// x -> v, e |- x : A+, G iff |- v : A+ and |- e : G 
type Env = map<string, Val>

// CEK Machine
// In state = Computation, Environment, stacK
// (E, C, K) : B-   iff   E |- G  and  G |- C : A-  and  G |- K : A- << B-
type     In  = (Env, Comp, Stack)
// TODO calculate Heap of In
datatype Out = Next(In) | Stuck | Terminal

// TODO: evaluation returns closed value?
// G |- V : A    D |- 
/*function EvalComp(env: Env, c: Comp) {
    match c
    
}*/

//todo define type of closure like Matt Might
function Eval(env: Env, val: Val): Val {
    match val
    case Var(x) => assume {:axiom} x in env; env[x]
    case _      => val
}

// Global environment works! Not sure how to handle when to look up value variables
// This function either steps the current state or tells you that it's terminal/stuck
// Type soundness = well-typed configs don't get stuck!
// TODO: replace * with Heap of state
// TODO: shouldn't stuck be auto-propagated?
function Step(state: In): Out reads * {
    var (env, comp, stack) := state;
    // Cases are organized as follows:
    // push/pop pairs (neg. elims & intros) and then
    // cases that don't touch the stack (pattern matching, refs)
    match comp
    // env |- G    G |- Bind(L, x, R) : A-    G |- K : A- << B-
    case Bind(lhs, var_, rhs) =>
    // env |- G    G |- L : Up(A+)
    // G, x : A+ |- N[x] : A-     G |- K : A- << B-
    //----------------------------------------------
    // G |- N[x] :: K : Up(A+) << B-
        Next((env, lhs, Push(Frame.Bind(var_, rhs), stack)))
    
    case Pure(val) => (
        match stack.Pop()
        // this is illegal because val is not closed
        case Some((Bind(var_, rhs), stack)) =>
            Next((env[var_ := Eval(env, val)], rhs, stack))
        
        case Some(_) => Stuck
        case None    => Terminal
    )

    // Function calls push the argument onto the stack...
    case Call(func, arg) =>
        Next((env, func, Push(Frame.Call(arg), stack)))
    
    // ...functions pop the argument off
    // that's why it's call-by-push-value
    // G |- e : D   D |- C : A-   D |- A- << B-
    case Func(bound, body) => (
        match stack.Pop()
        // this is illegal because arg has FV in D (not in G)
        // Close(arg): D |- V : A+  ~>  G |- [env]V : A+
        case Some((Call(arg), stack)) =>
            Next((env[bound := Eval(env, arg)], body, stack))
        
        case Some(_) => Stuck
        case None    => Terminal
    )

    // scrutinees need to be closed so that we can observe their value:
    // why doesn't Levy say this?

    case Ite(guard, then_, else_) => (
        match Eval(env, guard)
        case Bool(guard) =>
            Next((env, if guard then then_ else else_, stack))
        
        case _ => Stuck
    )

    case Read(ref) =>
        match Eval(env, ref) // this would now return a new environment...
        case New(ptr) => Next((env, ptr.deref, stack))
        
        case _        => Stuck
}

// Iterates step
method Run(s: In) decreases * {
    print("\n");
    match Step(s)
    case Next(s) => print s, "\n"; Run(s);
    case _ => print "done/stuck\n"; return;
}

// Initial configuration
function Initial(comp: Comp): In
    { (map[], comp, Empty) }

method Main() decreases * {
    /*Run(Initial(
        Comp.Bind(
            Pure(Bool(true)),
            "x",
            Ite(
                Var("x"),
                Pure(Bool(false)),
                Pure(Bool(true))
            )
        )
    ));*/
    /*Run(Initial(
        Comp.Call(
            Comp.Call(
                Comp.Func(
                    "x",
                    Comp.Func(
                        "y",
                        Pure(Var("x"))
                    )
                ),
                Bool(true)
            ),
            Bool(false)
        )
    ));*/
    // Verifies that lexical scope works
    var ptr := new Ptr(Func("y", Pure(Var("x"))));
    var fv := New(ptr);
    var fc := Read(Var("f"));
    var x1 := Int(1);
    var x2 := Int(2);
    var z  := Int(0);
    Run(Initial(
        Comp.Call(
        Comp.Call(
        Comp.Call(
        Func("x",
        Func("f",
        Func("x",
            Comp.Call(fc, z)))),
        x2),
        fv),
        x1)
    ));
}