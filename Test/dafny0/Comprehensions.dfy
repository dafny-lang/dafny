// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M()
{
  var numbers := set i | 0 <= i && i < 100;
  var squares := set i | 0 <= i && i < 100 :: Id(i)*i;  // verifying properties about set comprehensions with a term expression is hard

  assert 12 in numbers;
  assert Id(5) == 5;
  assert 25 in squares;
  assert 200 in numbers;  // error
}

function Id(x: int): int { x }  // for triggering

datatype D = A | B
// The following mainly test that set comprehensions can be compiled, but one would
// have to run the resulting program to check that the compiler is doing the right thing.
method Main()
{
  var q := set i,j | 0 <= i < 10 && 0 <= j < 3 :: i+j;
  PrintSet(q);
  q := set b: bool | true :: if b then 3 else 7;
  var d := set b:D | true;
  var test := forall d:D {:nowarn} :: d == A || d == B; // Ignoring the warning as we're only compiling here
  PrintSet(q);
  var m := set k | k in q :: 2*k;
  PrintSet(m);
  PrintSet(set k | k in q && k % 2 == 0);
  var sq := [30, 40, 20];
  PrintSet(set k, i | k in sq && 0 <= i < k && i % 7 == 0 :: k + i);
  var bb := forall k, i {:nowarn} | k in sq && 0 <= i < k && i % 7 == 0 :: k + i == 17; // Ignoring the warning as we're only compiling here
}

method PrintSet<T>(s: set<T>) {
  var q := s;
  while (q != {})
    decreases q;
  {
    var x :| x in q;
    print x, " ";
    q := q - {x};
  }
  print "\n";
}

// ---------- Regression tests ----------

method SetComprehensionBoxAntecedents()
{
  // The first assert below used to not verify, due to a missing $IsBox conjunct in the Boogie lambda
  // that encodes the set comprehension.
  var a := set x | x in {0,1,2,3,4,5} && x < 3;
  var b := {0,1,2};

  if
  case true =>
    assert a == b;
  case true =>
    assert forall x :: x in a ==> x in b;
    assert forall x :: x in b ==> x in a;
  case true =>
    assert forall x :: x in a <==> x in b;
}

// ---------- Sequence operations ----------

method Sequences0() {
  var four1s := [1, 1, 1, 1];
  var twelve1s := seq(12, _ => 1);
  assert twelve1s == four1s + four1s + four1s;

  var squares := seq(8, i => i*i);
  assert |squares| == 8;
  assert squares[6] == 36;
  if * {
    assert squares[7] == 0;  // error
  }

  var nats := seq(8, i => i);
}

class SeqOp {
  var x: real

  function G(i: nat): real
    reads this
  {
    if i < 20 then 2.5 else x
  }
  function H(i: nat): real
    reads if i < 20 then {} else {this}
  {
    if i < 20 then 2.5 else x
  }

  function S0(n: nat): seq<real> {
    seq(n, G)  // error: S0 reads {this}
  }
  function S1(n: nat): seq<real>
    reads this
  {
    seq(n, G)
  }
  function S2(n: nat): seq<real> {
    seq(n, H)  // error: S2 reads {this}
  }
  function S3(n: nat): seq<real>
    reads this
  {
    seq(n, H)
  }
  function S4(n: nat): seq<real> {
    seq(n, i => if i < 20 then 2.5 else x)  // error: lambda reads {this}
  }
  function S5(n: nat): seq<real> {
    seq(n, i reads this => if i < 20 then 2.5 else x)  // error: S5 reads {this}
  }
  function S6(n: nat): seq<real>
    reads this
  {
    seq(n, i reads this => if i < 20 then 2.5 else x)
  }
  function S7(n: nat): seq<real> {
    seq(n, i requires i < 20 => if i < 20 then 2.5 else x)  // error: S7 violates lambda's precondition
  }

  function T0(n: nat): seq<real>
    requires n <= 20
  {
    seq(n, G)  // error: T0 reads {this}
  }
  function T1(n: nat): seq<real>
    requires n <= 20
    reads this
  {
    seq(n, G)
  }
  function T2(n: nat): seq<real>
    requires n <= 20
  {
    seq(n, H)
  }
  function T3(n: nat): seq<real>
    requires n <= 20
  {
    seq(n, i reads this => if i < 20 then 2.5 else x)  // error: T3 reads {this}
  }
  function T4(n: nat): seq<real>
    requires n <= 20
  {
    seq(n, i requires i < 20 => if i < 20 then 2.5 else x)
  }
  function T5(n: nat): seq<real>
    requires n <= 20
  {
    seq(n, i reads if i < 20 then {} else {this} => if i < 20 then 2.5 else x)
  }

  function XT0(n: nat): seq<int> {
    seq<int>(n, _ => 7)
  }
  function XT1(n: nat): seq<int> {
    seq<nat>(n, _ => 7)
  }
  function XT2(n: nat): seq<int> {
    seq<nat>(n, _ => -7)  // error: -7 is not a nat
  }
  function XT3(n: nat): seq<nat> {
    seq(n, _ => -7)  // error: this is not a seq<nat>
  }
  function XT4(n: nat): seq<nat> {
    seq(n, i requires 0 <= i < 3 => 10)  // error: init function doesn't accept all indices
  }
  function XT5(n: nat): seq<nat> {
    seq(n, i requires 0 <= i < n => 10)
  }
  function XT6(n: nat): seq<nat> {
    seq(n, i => if i < n then 10 else -7)  // error: type of lambda is inferred to be int->nat, so the -7 gives an error
  }
  function XT7(n: nat): seq<nat> {
    seq(n, i => var u: int := if i < n then 10 else -7; u)  // fine: lambda has type int->int; use of this lambda always gives a nat
  }
  function XT8(n: nat): seq<nat> {
    seq(n, i => if i < n then -7 else 10)  // error: this can't be assigned to a seq<nat>
  }
  function XT9(n: nat): seq<nat> {
    seq<nat>(n, i => if i < n then -7 else 10)  // error: this can't be assigned to a seq<nat>
  }
}
