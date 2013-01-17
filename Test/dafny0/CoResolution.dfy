copredicate P(b: bool)
{
  !b && Q(null)
}

copredicate Q(a: array<int>)
{
  a == null && P(true)
}

//copredicate A() { B() }
//predicate B() { A() }  // error: SCC of a copredicate must include only copredicates

copredicate D()
  reads this;  // error: copredicates are not allowed to have a reads clause -- WHY NOT?
{
  true
}

copredicate S(d: set<int>)
{
  this.Undeclared#[5](d) &&  // error: 'Undeclared#' is undeclared
  Undeclared#[5](d) &&  // error: 'Undeclared#' is undeclared
  this.S#[5](d) &&
  S#[5](d) &&
  S#[_k](d)  // error: _k is not an identifier in scope
}

comethod CM(d: set<int>)
{
  var b;
  b := this.S#[5](d);
  b := S#[5](d);
  this.CM#[5](d);
  CM#[5](d);
}

module GhostCheck0 {
  codatatype Stream<G> = Cons(head: G, tail: Stream);
  method UseStream0(s: Stream)
  {
    var x := 3;
    if (s == s.tail) {  // error: this operation is allowed only in ghost contexts
      x := x + 2;
    }
  }
}
module GhostCheck1 {
  codatatype Stream<G> = Cons(head: G, tail: Stream);
  method UseStream1(s: Stream)
  {
    var x := 3;
    if (s ==#[20] s.tail) {  // this seems innocent enough, but it's currently not supported by the compiler, so...
      x := x + 7;  // error: therefore, this is an error
    }
  }
}
module GhostCheck2 {
  codatatype Stream<G> = Cons(head: G, tail: Stream);
  ghost method UseStreamGhost(s: Stream)
  {
    var x := 3;
    if (s == s.tail) {  // fine
      x := x + 2;
    }
  }
}
