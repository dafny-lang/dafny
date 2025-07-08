// RUN: %build "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Formula =
  | And(left: Formula, right: Formula)
  | Not(underlying: Formula)
  | True
{
  function size(): nat {
    match this
    case And(l, r) => l.size() + r.size()
    case Not(u) => u.size() + 1
    case True => 1
  }
}
