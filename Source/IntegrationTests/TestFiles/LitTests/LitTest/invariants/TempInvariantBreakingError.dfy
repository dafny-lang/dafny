// RUN: %exits-with 4 %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var x: int
  
  invariant x != 0

  constructor() {
     x := 1;
     x := 0; // breaking the invariant here is fine
     x := 1; // as long at it is satisfied at the end
  }

  method TemporarilyBreakInvariant()
    modifies this
  {
     x := 0; // temporarily breaking the invariant outside the constructor is allowed
     UseInvariant(this); // error: invariant doesn't hold here (force checked, since this is open)
     var me := this;
     UseInvariant(me); //  error: same as above (this can be copied as much as you want)
     x := 1;
  }
 
  static method UseInvariant(c: C) 
  {
    var y := 3 / c.x;
  }

  static method External(c: C)
  {
     UseInvariant(c);
  }

  static method External2(c: C)
    modifies c
  {
     c.x := 0; // verifier error: c's invariant cannot be re-established
  }
}