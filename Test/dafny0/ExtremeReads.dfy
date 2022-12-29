// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var data: int
  var next: C?
}

greatest predicate P(c: C?)
  requires c != null
  reads *
{
  c.next != null && P(c.next)
}

greatest predicate Q(c: C?)
  requires c != null
  reads c
{
  c.next != null && Q(c)
}

greatest predicate R(c: C?)
  reads c  // gratuitous
{
  R(c)
}

greatest lemma RAlwaysHolds(c: C?)
  ensures R(c)
{
}

method TestP(c: C?, e: C?)
  requires c != null && P(c)
  modifies c, e
{
  if
  case true =>
    assert P(c);  // yeah, we know it holds
  case true =>
    var d := new C;
    d.data := d.data + 1;
    assert P(c);  // a newly allocated object does not affect P(c)
  case e != null && e != c =>
    e.data := e.data + 1;  // change anything in the existing heap...
    assert P(c);  // error: ... and we no longer know if P(c) holds
  case true =>
    c.data := c.data + 1;
    assert P(c);  // error: same reason as above
}

method TestQ(c: C?, e: C?)
  requires c != null && Q(c)
  modifies c, e
{
  if
  case true =>
    assert Q(c);  // yeah, we know it holds
  case true =>
    var d := new C;
    d.data := d.data + 1;
    assert Q(c);  // we know it still holds, because the state of "c" is unchanged
  case e != null && e != c =>
    e.data := e.data + 1;
    assert Q(c);  // ditto
  case true =>
    c.data := c.data + 1;
    assert Q(c);  // error: can't tell it's still the same
}

method TestR(c: C?)
  requires c != null && R(c)
  modifies c
{
  if
  case true =>
    c.data := c.data + 1;
    RAlwaysHolds(c);
    assert R(c);  // we know R(c) holds, because of the lemma
  case true =>
    c.data := c.data + 1;
    assert R(c);  // error: can't tell it's still the same
}

least predicate V(c: C?)
  reads c
{
  V(c)
}

least lemma VNeverHolds(c: C?)
  requires V(c)
  ensures false
{
}

method TestV(c: C?)
  requires c != null && V(c)
  modifies c
{
  if
  case true =>
    c.data := c.data + 1;
    assert V(c);  // error: can't tell if V(c) holds here
  case true =>
    VNeverHolds(c);
    c.data := c.data + 1;
    assert V(c);  // by lemma VNeverHolds, we know we never get here, so we can prove anything
}

// ---- Now for the generated prefix predicates

method TestPrefixPredicatesP(k: ORDINAL, c: C?, e: C?)
  requires c != null && P#[k](c)
  modifies c, e
{
  if
  case true =>
    assert P#[k](c);  // yeah, we know it holds
  case true =>
    var d := new C;
    d.data := d.data + 1;
    assert P#[k](c);  // a newly allocated object does not affect P(c)
  case e != null && e != c =>
    e.data := e.data + 1;  // change anything in the existing heap...
    assert P#[k](c);  // error (x2): ... and we no longer know if P(c) holds
  case true =>
    c.data := c.data + 1;
    assert P#[k](c);  // error (x2): same reason as above
}

method TestPrefixPredicatesQ(k: ORDINAL, c: C?, e: C?)
  requires c != null && Q#[k](c)
  modifies c, e
{
  if
  case true =>
    assert Q#[k](c);  // yeah, we know it holds
  case true =>
    var d := new C;
    d.data := d.data + 1;
    assert Q#[k](c);  // we know it still holds, because the state of "c" is unchanged
  case e != null && e != c =>
    e.data := e.data + 1;
    assert Q#[k](c);  // ditto
  case true =>
    c.data := c.data + 1;
    assert Q#[k](c);  // error (x2): can't tell it's still the same
}

method TestPrefixPredicatesR(k: ORDINAL, c: C?)
  requires c != null && R#[k](c)
  modifies c
{
  if
  case true =>
    c.data := c.data + 1;
    RAlwaysHolds#[k](c);
    assert R#[k](c);  // we know R#[k](c) holds, because of the lemma
  case true =>
    c.data := c.data + 1;
    RAlwaysHolds#[k+7](c);
    assert R#[k+7](c);  // the lemma tells us this, too (regardless of whether or not we know R#[k](c) on entry to the method)
  case true =>
    c.data := c.data + 1;
    RAlwaysHolds#[k+7](c);
    assert R#[k](c);  // error (x2): the lemma doesn't immediately tell us this
  case true =>
    c.data := c.data + 1;
    assert R#[k](c);  // error (x2): can't tell it's still the same
}

method TestPrefixPredicatesV(k: ORDINAL, c: C?)
  requires c != null && V#[k](c)
  modifies c
{
  if
  case true =>
    c.data := c.data + 1;
    assert V#[k](c);  // error (x2): can't tell if V(c) holds here
  case true =>
    VNeverHolds#[k](c);
    c.data := c.data + 1;
    assert V#[k](c);  // by lemma VNeverHolds, we know we never get here, so we can prove anything
}
