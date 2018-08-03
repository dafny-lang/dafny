// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function method {:simplifier} simp<T>(t: T): T { t }

function method {:opaque} Foo(x: int): int
{
  42
}

lemma {:simp} Foo_42(x: int)
  ensures Foo(7) == 42
{
  reveal Foo();
}

datatype List<T> = Cons(car: T, cdr: List<T>) | LNil
predicate method InList<T(==)>(l: List<T>, x: T)
  decreases l
{
    if l.LNil? then false else
      x == l.car || InList(l.cdr, x)
}
function method Length<T>(l: List<T>): nat
  decreases l
{
  if l.LNil? then 0 else 1 + Length(l.cdr)
}
datatype Option<T> = Some(val: T) | None
datatype Pair<T,U> = Pair(car: T, cdr: U)

function method {:opaque} AssocGet<T(==),U>(l: List<Pair<T,U>>, x: T): Option<U>
    decreases l
{
    if l.LNil? then None else
    if l.car.car == x then Some(l.car.cdr) else
    AssocGet(l.cdr, x)
}
function method AssocSet<T(==),U>(l: List<Pair<T,U>>, x: T, v: U): List<Pair<T,U>>
{
    Cons(Pair(x, v), l)
}

type Var = string
type Val = int

datatype Expr =
  Var(name: string) |
  Lit(val: int) |
  Add(x: Expr, y: Expr) |
  Sub(x: Expr, y: Expr) |
  Mul(x: Expr, y: Expr)

type Context = List<Pair<Var, Val>>

function method {:opaque} /* {:simp} */ Eval_Var(x: Var, ctx: Context): Val
{
  var get := AssocGet(ctx, x);
  if get.Some?
    then get.val
    else 999
}

lemma {:simp} Eval_Var_def(x: Var, ctx: Context)
  ensures
  Eval_Var(x, ctx) ==
  var get := AssocGet(ctx, x);
  if get.Some?
    then get.val
  else 999
  {
    reveal Eval_Var();
  }


function method {:opaque} Eval(e: Expr, ctx: List<Pair<Var, Val>>): int
{
  match e
    case Add(e1, e2) => Eval(e1, ctx) + Eval(e2, ctx)
    case Sub(e1, e2) => Eval(e1, ctx) - Eval(e2, ctx)
    case Mul(e1, e2) => Eval(e1, ctx) * Eval(e2, ctx)
    case Lit(i) => i
    case Var(x) => Eval_Var(x, ctx)
}

lemma {:simp} Eval_Add(e1: Expr, e2: Expr, ctx: Context)
  ensures Eval(Add(e1, e2), ctx) == Eval(e1, ctx) + Eval(e2, ctx)
{
  reveal Eval();
}

lemma {:simp} Eval_Lit(i: int, ctx: Context)
  ensures Eval(Lit(i), ctx) == i
{
  reveal Eval();
}

lemma {:simp} AssocGet_Cons<K, V>(x: K, v: V, ps: List<Pair<K, V>>, k: K)
  ensures
  AssocGet(Cons(Pair(x, v), ps), k) ==
  if x == k then Some(v) else AssocGet(ps, k)
{
  reveal AssocGet();
}

lemma {:simp} Eval_Var_simp(x: Var, ctx: Context)
  ensures Eval(Var(x), ctx) == Eval_Var(x, ctx)
{
  reveal Eval();
}


ghost method test(x: int) {
  assert simp(var ctx := Cons(Pair("x", x), LNil); Eval(Add(Var("x"), Add(Var("x"), Var("x"))), ctx)) ==
  3 * x;
}
