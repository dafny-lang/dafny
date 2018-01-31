// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
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

function method Id(x: int): int { x }  // for triggering

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
