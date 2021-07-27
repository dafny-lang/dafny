// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var more: C?
  constructor ()
    ensures more == null || fresh(more)
  {
    if * {
      more := null;
    } else {
      more := this;
    }
  }
  static method MaybeNew() returns (c: C?)
    ensures c == null || (fresh(c) && (c.more == null || fresh(c.more)))
  {
    if * {
      c := new C();
    } else {
      c := null;
    }
  }
}

method Test0()
{
  var c := C.MaybeNew();
  // The following once omitted the well-formedness check
  modify c.more; // error: c may be null
}

method Test1()
{
  var c := C.MaybeNew();
  // The following once omitted the well-formedness check
  modify c.more { // error: c may be null
    if c != null && c.more != null {
      c.more.more := null;
    }
  }
}

method Test2(c: C?)
  modifies c.more // error: c may be null
{
}

method Test3() {
  // The following once omitted the well-formedness check
  modify (if 1/0 > 0 then {} else {}); // error: division by zero
}

method Test4(n: nat) {
  var c := C.MaybeNew();
  var i := 0;
  while i < n
    // The following once omitted the well-formedness check
    modifies c.more // error: c may be null
  {
    i := i + 1;
  }
}

method Test5(n: nat) {
  var c := C.MaybeNew();
  var i := 0;
  while
    // The following once omitted the well-formedness check
    modifies c.more // error: c may be null
    decreases n - i
  {
    case i < n => i := i + 1;
  }
}

method Test6(n: nat) {
  var c := C.MaybeNew();
  for i := 0 to n
    // The following once omitted the well-formedness check
    modifies c.more // error: c may be null
  {
  }
}

function method F(c: C?): int
  reads c, c.more // error: c may be null
{
  5
}

iterator Iter(c: C?, d: C?)
  modifies c.more // error: c may be null (reported twice)
  reads d.more // error: c may be null (reported twice)
{
}

method Fresh() {
  var c := C.MaybeNew();
  ghost var b := fresh(c.more); // error: c may be null
}

method Unchanged(c: C?)
  modifies c
{
  assert unchanged(c.more); // error (3x): c may be null, c.more may be null, c.more may not be allocated
}
