// Celebrity example, inspired by the Rodin tutorial

static function method Knows<Person>(a: Person, b: Person): bool
  requires a != b;  // forbid asking about the reflexive case

static function IsCelebrity<Person>(c: Person, people: set<Person>): bool
{
  c in people &&
  (forall p :: p in people && p != c ==> Knows(p, c) && !Knows(c, p))
}

method FindCelebrity0<Person>(people: set<Person>, ghost c: Person) returns (r: Person)
  requires exists c :: IsCelebrity(c, people);
  ensures r == c;
{
  var cc; assume cc == c;  // this line essentially converts ghost c to non-ghost cc
  r := cc;
}

method FindCelebrity1<Person>(people: set<Person>, ghost c: Person) returns (r: Person)
  requires IsCelebrity(c, people);
  ensures r == c;
{
  var Q := people;
  var x := choose Q;
  while (Q != {x})
    //invariant Q <= people;  // inv1 in Rodin's Celebrity_1, but it's not needed here
    invariant IsCelebrity(c, Q);  // inv2
    invariant x in Q;
    decreases Q;
  {
    var y := choose Q - {x};
    if (Knows(x, y)) {
      Q := Q - {x};  // remove_1
    } else {
      Q := Q - {y};  assert x in Q;  // remove_2
    }
    x := choose Q;
  }
  r := x;
}

method FindCelebrity2<Person>(people: set<Person>, ghost c: Person) returns (r: Person)
  requires IsCelebrity(c, people);
  ensures r == c;
{
  var b := choose people;
  var R := people - {b};
  while (R != {})
    invariant R <= people;  // inv1
    invariant b in people;  // inv2
    invariant b !in R;  // inv3
    invariant IsCelebrity(c, R + {b});  // my non-refinement way of saying inv4

    decreases R;
  {
    var x := choose R;
    if (Knows(x, b)) {
      R := R - {x};
    } else {
      b := x;
      R := R - {x};
    }
  }
  r := b;
}

method FindCelebrity3(n: int, people: set<int>, ghost c: int) returns (r: int)
  requires 0 < n;
  requires (forall p :: p in people <==> 0 <= p && p < n);
  requires IsCelebrity(c, people);
  ensures r == c;
{
  r := 0;
  var a := 1;
  var b := 0;
  while (a < n)
    invariant a <= n;
    invariant b < a;  // Celebrity_2/inv3 and Celebrity_3/inv2
    invariant c == b || (a <= c && c < n);
  {
    if (Knows(a, b)) {
      a := a + 1;
    } else {
      b := a;
      a := a + 1;
    }
  }
  r := b;
}
