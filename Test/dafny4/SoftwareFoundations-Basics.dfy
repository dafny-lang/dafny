// RUN: %exits-with 4 %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Basics.v done in Dafny

// Enumerated Types

// Days of the Week

datatype day =
    monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday

// See method test_next_weekday() below for an explanation of why this function
// is declared a non-ghost (by "function method").
function method next_weekday (d:day) : day
{
  match d
  case monday    => tuesday
  case tuesday   => wednesday
  case wednesday => thursday
  case thursday  => friday
  case friday    => monday
  case saturday  => monday
  case sunday    => monday
}

method test_next_weekday()
{
  assert next_weekday(friday) == monday;
  assert next_weekday(next_weekday(saturday)) == tuesday;
  // Note, if you're not sure what some expression will compute, you
  // can assert that it equals some arbitrary value of the correct type.
  // For example:
  var d := next_weekday(next_weekday(tuesday));
  assert d == friday;   // error (use the Verification Debugger to view the correct value)
  // You will then get an error message (unless you were lucky and
  // happened to pick the right value).  If you're running the Dafny IDE
  // in Visual Studio, you can then click on the red circle that signals
  // the error.  This will bring up the Verification Debugger, where you
  // can inspect the value of d.  Then try changing the assertion in
  // the program to assert d to equal it.  In some cases, depending on
  // how many Dafny knows about the value you're trying to get it to
  // compute, you may need to build a disjunction of values for d in the
  // assertion.
  // Or, just write a program that prints the value, compile the program,
  // and run it -- Dafny is a programming language after all.  (Note, by
  // default, functions in Dafny of "ghost", which means they don't turn
  // into compiled code.  If you want to compile code for next_weekday, so
  // that you can use it in a print statement, change "function" to
  // "function method" in the declaration of next_weekday.)  To try this
  // out:  (0) comment out (or fix!) the assert above
  // so that the program will verify, (1) fill in a body of the uninterpreted
  // function f on line 396 below (any body will do; for example, uncomment
  // line 400), and (2) change the name of this method to Main().
  print next_weekday(wednesday);
}



// Booleans

// Booleans are built into Dafny as primitives.  Nevertheless, here is
// another definition, using an enumeration.

datatype Bool = True | False

function negb (b:Bool) : Bool
{
  match b
  case True => False
  case False => True
}

function andb (b1:Bool, b2:Bool) : Bool
{
  match b1
  case True => b2
  case False => False
}

function orb (b1:Bool, b2:Bool) : Bool
{
  match b1
  case True => True
  case False => b2
}

method test_orb()
{
  assert orb(True, False) == True;
  assert orb(False, False) == False;
  assert orb(False, True) == True;
  assert orb(True, True) == True;
}

// Exercise: 1 star (nandb)

function nandb (b1:Bool, b2:Bool) : Bool
{
  negb(andb(b1, b2))
}

method test_nandb()
{
  assert nandb(True, False) == True;
  assert nandb(False, False) == True;
  assert nandb(False, True) == True;
  assert nandb(True, True) == False;
}

// Exercise: 1 star (andb3)

function andb3 (b1:Bool, b2:Bool, b3:Bool) : Bool
{
  andb(andb(b1, b2), b3)
}

method test_andb3()
{
  assert andb3(True, True, True) == True;
  assert andb3(False, True, True) == False;
  assert andb3(True, False, True) == False;
  assert andb3(True, True, False) == False;
}

// Function Types

// Numbers

datatype Nat =
    O
  | S(Nat)

function pred (n : Nat) : Nat
{
  match n
  case O => O
  case S(n') => n'
}

function minustwo (n : Nat) : Nat
{
  match n
  case O => O
  case S(nn) =>
    // Note, Dafny currently does not support nested patterns in match expressions, but
    // this will change soon.
    match nn
    case O => O
    case S(n') => n'
}

function evenb (n:Nat) : Bool
{
  match n
  case O       => True
  case S(nn) =>
    match nn
    case O     => False
    case S(n') => evenb(n')
}

function oddb (n:Nat) : Bool
{
  negb(evenb(n))
}

method test_oddb()
{
  assert oddb(S(O)) == True;
  assert oddb(S(S(S(S(O))))) == False;
}

function plus (n : Nat, m : Nat) : Nat
{
  match n
  case O => m
  case S(n') => S(plus(n', m))
}

method test_plus()
{
  assert plus(S(S(S(O))), S(S(O))) == S(S(S(S(S(O)))));
}

function mult (n: Nat, m: Nat) : Nat
{
  match n
  case O => O
  case S(n') => plus(m, mult(n', m))
}

method test_mult()
{
  var n3 := S(S(S(O)));
  var n9 := S(S(S(S(S(S(S(S(S(O)))))))));
  assert mult(n3, n3) == n9;
}

function minus (n: Nat, m: Nat) : Nat
{
  match n
  case O => O
  case S(n') =>
    match m
    case O => n
    case S(m') => minus(n', m')
}

function exp (base: Nat, power: Nat) : Nat
{
  match power
  case O => S(O)
  case S(p) => mult(base, exp(base, p))
}

// Exercise: 1 star (factorial)

function factorial(n: Nat): Nat
{
  match n
  case O => S(O)
  case S(n') => mult(n, factorial(n'))
}

method test_factorial1()
{
  var n2 := S(S(O));
  var n3 := S(n2);
  var n5 := S(S(n3));
  var n6 := S(n5);
  assert factorial(n3) == n6;

  var n10 := S(S(S(S(n6))));
  var n12 := S(S(n10));

  assert factorial(n5)==mult(n10, n12);
}

method test_factorial1_old()
{
  var n2 := S(S(O));
  var n3 := S(n2);
  var n5 := S(S(n3));
  var n6 := S(n5);
  assert factorial(n3) == n6;

  var n10 := S(S(S(S(n6))));
  var n12 := S(S(n10));

  // proving that 5! == 10*12 _used to_ take some effort...
  calc {
    factorial(n5);
  ==  { mult_lemma(n2, n6); }
    mult(n5, plus(plus(n6, n6), plus(plus(n6, n6), O)));
  ==  { mult_lemma(n5, plus(n6, n6)); }
    mult(n10, n12);
  }
}

// This lemma expresses:  m*(2*n) == (2*m)*n
lemma {:vcs_split_on_every_assert} mult_lemma(m: Nat, n: Nat)
  ensures mult(m, plus(n, n)) == mult(plus(m, m), n)
{
  match m {
    case O =>
    case S(m') =>
      calc {
        mult(m, plus(n, n));
      ==
        plus(plus(n, n), mult(m', plus(n, n)));
      ==  // induction hypothesis
        plus(plus(n, n), mult(plus(m', m'), n));
      ==  { assert forall a,b,c {:induction} :: plus(plus(a, b), c) == plus(a, plus(b, c)); }
        plus(n, plus(n, mult(plus(m', m'), n)));
      ==
        mult(S(S(plus(m', m'))), n);
      ==
        mult(S(plus(S(m'), m')), n);
      ==  { assert forall a,b {:induction} :: S(plus(a, b)) == plus(a, S(b)); }
        mult(plus(S(m'), S(m')), n);
      }
  }
}

function beq_nat (n: Nat, m: Nat) : Bool
{
  match n
  case O => (
         match m
         case O => True
         case S(m') => False
         )
  case S(n') =>
         match m
         case O => False
         case S(m') => beq_nat(n', m')
}

function ble_nat (n: Nat, m: Nat) : Bool
{
  match n
  case O => True
  case S(n') =>
      match m
      case O => False
      case S(m') => ble_nat(n', m')
}

method test_ble_nat1()
{
  var n2 := S(S(O));
  var n4 := S(S(n2));
  assert ble_nat(n2, n2) == True;
  assert ble_nat(n2, n4) == True;
  assert ble_nat(n4, n2) == False;
}

// Exercise: 2 stars (blt_nat)

function blt_nat (n: Nat, m: Nat) : Bool
{
  andb(ble_nat(n, m), negb(beq_nat(n, m)))
}

method test_blt_nat1()
{
  var n2 := S(S(O));
  var n4 := S(S(n2));
  assert blt_nat(n2, n2) == False;
  assert blt_nat(n2, n4) == True;
  assert blt_nat(n4, n2) == False;
}

// Proof by Simplification

lemma plus_O_n (n: Nat)
  ensures plus(O, n) == n
{
}

lemma plus_1_l (n: Nat)
  ensures plus(S(O), n) == S(n)
{
}

lemma mult_0_l (n: Nat)
  ensures mult(O, n) == O
{
}

// Proof by Rewriting

lemma plus_id_example (n: Nat, m: Nat)
  ensures n == m ==> plus(n, n) == plus(m, m)
{
}

// Exercise: 1 star (plus_id_exercise)

lemma plus_id_exercise (n: Nat, m: Nat, o: Nat)
  ensures n == m ==> m == o ==> plus(n, m) == plus(m, o)
{
}

lemma mult_0_plus (n: Nat, m: Nat)
  ensures mult(plus(O, n), m) == mult(n, m)
{
}

// Exercise: 2 stars (mult_S_1)

lemma mult_S_1 (n: Nat, m: Nat)
  ensures m == S(n) ==> mult(m, plus(S(O), n)) == mult(m, m)
{
}


// Proof by Case Analysis

lemma plus_1_neq_0_firsttry (n: Nat)
  ensures beq_nat(plus(n, S(O)), O) == False
{
}

lemma plus_1_neq_0 (n: Nat)
  ensures beq_nat(plus(n, S(O)), O) == False
{
}

lemma negb_involutive (b: Bool)
  ensures negb(negb(b)) == b
{
}

// Exercise: 1 star (zero_nbeq_plus_1)

lemma zero_nbeq_plus_1 (n: Nat)
  ensures beq_nat(O, plus(n, S(O))) == False
{
}

// More Exercises

// Exercise: 2 stars (boolean functions)

// Since Dafny currently does not allow functions as parameters, we instead declare
// a global function f for use in the following lemmas.  Since f is given no body,
// it will be treated as an uninterpreted function.
function f(x: Bool): Bool
// Note:  If you want to compile and run the program, as suggested above in method
// test_next_weekday, then you must supply some body for f.  Here is one way to do
// that:
//      { x }

lemma identity_fn_applied_twice(b: Bool)
  requires forall x :: f(x) == x
  ensures f(f(b)) == b
{
}


lemma negation_fn_applied_twice(b: Bool)
  requires forall x :: f(x) == negb(x)
  ensures f(f(b)) == b
{
}

// Exercise: 2 stars (andb_eq_orb)

lemma andb_true (b : Bool)
  ensures andb(True, b) == b
{
}

lemma orb_false (b : Bool)
  ensures orb(False, b) == b
{
}

lemma andb_eq_orb (b: Bool, c: Bool)
  ensures andb(b, c) == orb(b, c) ==> b == c
{
}

// Exercise: 3 stars (binary)

datatype bin = Zero | Twice(bin) | TwicePlusOne(bin)

function increment(b: bin): bin
{
  match b
  case Zero => TwicePlusOne(Zero)
  case Twice(b') => TwicePlusOne(b')
  case TwicePlusOne(b') => Twice(increment(b'))
}

function BinToUnary(b: bin): Nat
{
  match b
  case Zero => O
  case Twice(b') =>
    var t := BinToUnary(b');
    plus(t, t)
  case TwicePlusOne(b') =>
    var t := BinToUnary(b');
    plus(t, plus(t, S(O)))
}

method test_bin()
{
  var n6 := S(S(S(S(S(S(O))))));
  var n13 := S(S(S(S(S(S(S(n6)))))));
  assert BinToUnary(Twice(TwicePlusOne(TwicePlusOne(Zero)))) == n6;
  assert BinToUnary(TwicePlusOne(Twice(TwicePlusOne(TwicePlusOne(Zero))))) == n13;
}

method test_increment()
{
  var b13 := TwicePlusOne(Twice(TwicePlusOne(TwicePlusOne(Zero))));
  var n13 := S(S(S(S(S(S(S(S(S(S(S(S(S(O)))))))))))));
  var n14 := S(n13);

  assert increment(Twice(TwicePlusOne(TwicePlusOne(Zero)))) == TwicePlusOne(TwicePlusOne(TwicePlusOne(Zero)));
  assert increment(b13) == Twice(TwicePlusOne(TwicePlusOne(TwicePlusOne(Zero))));

  assert BinToUnary(increment(b13)) == plus(BinToUnary(b13), S(O));
}

// Optional Material

// [Fixpoint]s and Structural Recursion

function plus' (n : Nat, m : Nat) : Nat
{
  match n
  case O => m
  case S(n') => S(plus'(n', m))
}

// Exercise: 2 stars, optional (decreasing)

function decreasingOnTwo (n: Nat, m: Nat, p: Nat) : Nat
{
  match p
  case O => (
      match n
      case O     => O
      case S(n') => decreasingOnTwo(n', m, S(O))
      )
  case S(_) =>
      match m
      case O     => S(O)
      case S(m') => decreasingOnTwo(n, m', O)
}
