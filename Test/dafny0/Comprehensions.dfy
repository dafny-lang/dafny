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

// The following mainly test that set comprehensions can be compiled, but one would
// have to run the resulting program to check that the compiler is doing the right thing.
method Main()
{
  var q := set i,j | 0 <= i && i < 10 && 0 <= j && j < 3 :: i+j;
  PrintSet(q);
  q := set b: bool | true :: if b then 3 else 7;
  PrintSet(q);
  var m := set k | k in q :: 2*k;
  PrintSet(m);
  PrintSet(set k | k in q && k % 2 == 0);
  var sq := [30, 40, 20];
  PrintSet(set k, i | k in sq && 0 <= i && i < k && i % 7 == 0 :: k + i);
  var bb := forall k, i | k in sq && 0 <= i && i < k && i % 7 == 0 :: k + i == 17;
}

method PrintSet<T>(s: set<T>) {
  var q := s;
  while (q != {})
    decreases q;
  {
    var x := choose q;
    print x, " ";
    q := q - {x};
  }
  print "\n";
}
