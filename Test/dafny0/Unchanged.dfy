// RUN: %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var f: int
  var g: int


  method M(c: C, d: C, x: int)
    modifies this, c
  {
    c.f := c.f + x;
    assert x != 0 ==> !unchanged(c);
    assert x != 0 ==> !unchanged(c`f);
    assert d != c ==> unchanged(d);
    assert unchanged(d`g);
    assert unchanged(`g);
    assert unchanged(c`g);
    var R := {this,d};
    assert unchanged(c`g);
    assert unchanged(R`g);
    assert c != this && c != d ==> unchanged(R);
    c.f := c.f - x;
    assert unchanged(c);
    assert unchanged(R);
  }

  method N(c: C, d: C, x: int)
    modifies this, c
  {
    c.f := c.f + 1;
    if
    case true =>  assert unchanged(c);  // error
    case true =>  assert unchanged(d);  // error: d could equal c
    case true =>  assert unchanged(c`f);  // error
    case true =>
      c.g := c.g + x;
      assert unchanged(c`g);  // error: x could be non-zero
  }
  method New()
  {
    var c: C := new C;
    if
    case true =>  assert unchanged(this);  
    case true =>  assert unchanged(c);  // error: 'alloc' changed
    case true =>  assert unchanged(c`f);  // error: 'alloc' changed
    case true =>  assert unchanged(this, c);  // error: 'alloc' changed for 'c'
    case true =>  assert unchanged(c, this);  // error: 'alloc' changed for 'c'
  }
}
