class C<U> {
  method M<T>(x: T, u: U) returns (y: T)
    ensures x == y && u == u;
  {
    y := x;
  }

  function method F<X>(x: X, u: U): bool
  {
    x == x && u == u
  }

  method Main(u: U)
  {
    var t := F(3,u) && F(this,u);
    call kz := M(t,u);
    assert kz && (G() || !G());
  }

  function G<Y>(): Y;
}

class SetTest {
  method Add<T>(s: set<T>, x: T) returns (t: set<T>)
    ensures t == s + {x};
  {
    t := s + {x};
  }

  method Good()
  {
    var s := {2, 5, 3};
    call t := Add(s, 7);
    assert {5,7,2,3} == t;
  }

  method Bad()
  {
    var s := {2, 50, 3};
    call t := Add(s, 7);
    assert {5,7,2,3} == t;  // error
  }
}

class SequenceTest {
  method Add<T>(s: seq<T>, x: T) returns (t: seq<T>)
    ensures t == s + [x];
  {
    t := s + [x];
  }

  method Good()
  {
    var s := [2, 5, 3];
    call t := Add(s, 7);
    assert [2,5,3,7] == t;
  }

  method Bad()
  {
    var s := [2, 5, 3];
    call t := Add(s, 7);
    assert [2,5,7,3] == t || [2,5,3] == t;  // error
  }
}

// -------------------------

class CC<T> {
  var x: T;
  method M(c: CC<T>, z: T) returns (y: T)
    requires c != null;
    modifies this;
    ensures y == c.x && x == z;
  {
    x := c.x;
    x := z;
    y := c.x;
  }
}

class CClient {
  method Main() {
    var c := new CC<int>;
    var k := c.x + 3;
    if (c.x == c.x) {
      k := k + 1;
    }
    var m := c.x;
    if (m == c.x) {
      k := k + 1;
    }
    c.x := 5;
    c.x := c.x;
    call z := c.M(c, 17);
    assert z == c.x;
  }
}

// -------------------------

static function IsCelebrity<Person>(c: Person, people: set<Person>): bool;
  requires c == c || c in people;

method FindCelebrity3(people: set<int>, ghost c: int)
  requires IsCelebrity(c, people);  // once upon a time, this caused the translator to produce bad Boogie
{
  ghost var b: bool;
  b := IsCelebrity(c, people);
  b := F(c, people);
}

static function F(c: int, people: set<int>): bool;
  requires IsCelebrity(c, people);

function RogerThat<G>(g: G): G
{
  g
}

function Cool(b: bool): bool
{
  b
}

method IsRogerCool(n: int)
  requires RogerThat(true);  // once upon a time, this caused the translator to produce bad Boogie
{
  if (*) {
    assert Cool(2 < 3 && n < n && n < n+1);  // the error message here will peek into the argument of Cool
  } else if (*) {
    assert RogerThat(2 < 3 && n < n && n < n+1);  // same here; cool, huh?
  }
}
