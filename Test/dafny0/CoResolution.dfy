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
  this.S#(d) &&  // error: the call to S# must give an explicit depth argument
  S#(d) &&  // error: the call to S# must give an explicit depth argument
  this.Undeclared#(d) &&  // error: 'Undeclared#' is undeclared, and depth argument is left implicit
  this.Undeclared#[5](d) &&  // error: 'Undeclared#' is undeclared
  Undeclared#(d) &&  // error: 'Undeclared#' is undeclared, and depth argument is left implicit
  Undeclared#[5](d) &&  // error: 'Undeclared#' is undeclared
  this.S#[5](d) &&
  S#[5](d) &&
  S#(5, d) &&  // error: the '5' here does not give the depth argument
  S#[_k](d)  // error: _k is not an identifier in scope
}

comethod CM(d: set<int>)
{
  var b;
  b := this.S#[5](d) && this.S#(d + d);  // error: cannot rely on implicit depth argument here
  b := S#[5](d) && S#(d + d);  // error: cannot rely on implicit depth argument here
  this.CM#[5](d);
  CM#[5](d);
  this.CM#(d + d);  // error: must give an explicit depth argument
  CM#(d + d);  // error: must give an explicit depth argument
}
