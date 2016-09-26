// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/* SOON
class U {
  var aa: int
  var bb: int
  var next: U
    
  static twostate function H(x: int, new u: object): real
  {
    x as real
  }

  twostate predicate R(y: real, new u: object)
  {
    y.Floor == y as int
  }
  
  twostate function G(x: int, new u: object): real
    requires this != u
    requires old(aa) <= aa && unchanged(`bb)
    reads this
    ensures old(aa) <= aa && old(G(x, u)) == G(x, u)
    decreases old(aa) - old(aa) + x
  {
    if 0 < x then
      G(x-1, u)
    else
      x as real
  }
}
 */
