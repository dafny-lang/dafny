// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"

// Regression tests: a recursive self-call in a function's specification used to
// allow proving false, because CanCallAssumption dropped the self-call allowance
// (cco) on some sub-expressions. Several surface forms hit the same root cause:
// - #6405: a match expression on a single-constructor datatype, which the
//   MatchFlattener lowers to a LetExpr.
// - #6343: a `var` expression, which is already a LetExpr.
// - a revealed `const` field whose definition is inlined when the field is
//   selected on the result of a self-call (MemberSelectExpr / ConstantField).
// - a `var ... :| ...` (let-such-that) whose such-that constraint contains a
//   self-call (the standalone $let#canCall axiom).

datatype D = Pair(x: int, y: int)

function f(): D
  ensures match f() {case Pair(a, b) => a >= 0}
  ensures false
{ Pair(0, 0) }

// Also test that legitimate uses still verify:
function g(): D
  ensures match g() {case Pair(a, b) => a >= 0}
{ Pair(0, 0) }

// #6343: `var` in ensures with a recursive self-call.
function h(elements: int): (r: int)
  ensures var i := 1; h(elements) == 0
{ 1 }

// Legitimate `var` in ensures:
function k(elements: int): (r: int)
  ensures var i := 1; r >= i - 1
{ 1 }

datatype Wrapper = Wrap(val: int) {
  const c: int := this.val
}

// Const field selected on the result of a self-call must not let `false` be proved.
function constField(n: int): Wrapper
  ensures constField(n).c == 0
  ensures false
{ Wrap(0) }

// Legitimate const-field selection on a self-call still verifies.
function constFieldOk(n: int): Wrapper
  ensures constFieldOk(n).c == 0
{ Wrap(0) }

// Let-such-that with a self-call in the constraint must not let `false` be proved.
function letSuchThat(): int
  ensures var x: int :| x == letSuchThat(); true
  ensures false
{ 1 }

// Parameterless predicate variant.
predicate letSuchThatPred()
  ensures var x: int :| x == 0 && letSuchThatPred(); true
  ensures false
{ true }

// Legitimate let-such-that whose body relies on the witness equality still verifies.
function letSuchThatOk(n: nat): nat
  ensures var x :| x == letSuchThatOk(n); x == letSuchThatOk(n)
{ 0 }

// The self-call allowance must also be withheld when the trivial self-call reaches the function through a
// let-bound alias of a formal, or of "this": the constraint's free variables are then the alias, so the formal
// (or "this") is absent from the axiom's scope, and an allowance keyed on its presence would leak.
function aliasedFormal(n: int): int
  ensures var a := n; var x: int :| x == aliasedFormal(a); x == aliasedFormal(a)
  ensures false  // must NOT be provable from the such-that above
{ 1 }

class Aliased {
  function aliasedThis(): int
    ensures var t := this; var x: int :| x == t.aliasedThis(); x == t.aliasedThis()
    ensures false  // must NOT be provable from the such-that above
  { 1 }
}

// Conversely, a self-call on a receiver or with an argument that genuinely is out of the axiom's scope must
// still translate (the conjunct is simply omitted), rather than emitting an undeclared identifier.
class OutOfScopeReceiver {
  function f(o: OutOfScopeReceiver, n: nat): int
    decreases n
    ensures n > 0 ==> var x: int :| x == o.f(o, n - 1); true
  { 0 }
}

function outOfScopeFormal(n: nat, m: int): int
  decreases n
  ensures n > 0 ==> var x: int :| x == outOfScopeFormal(n - 1, n); true
{ 0 }

// Propagating the allowance into these sub-expressions must not also suppress the $IsA# facts a datatype
// equality contributes there (see CanCallOptions.AllowanceOnly): without them, the case analysis over D's
// constructors is unavailable and the assertion below is not provable.
datatype Two = A(a: int) | B(b: int)

ghost function pick(n: int): int
{ var z: int :| z == 0 && mk(n) == mk(n); z }

function mk(n: int): Two

predicate Q(d: Two)

lemma IsAFactsSurvive(n: int)
  requires forall a: int :: Q(A(a))
  requires forall b: int :: Q(B(b))
{
  var q := pick(n);
  assert Q(mk(n));
}
