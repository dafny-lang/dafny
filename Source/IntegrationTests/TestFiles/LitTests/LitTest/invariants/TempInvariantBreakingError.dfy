// RUN: %exits-with 4 %verify --type-system-refresh --check-invariants --reads-clauses-on-methods "%s" > "%t"
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
     if * {
       UseInvariant(this); // error: invariant doesn't hold here (force checked, since this is open)
     } else {
       var me := this;
       MethodReadsNothing();
       var _ := FunctionReadsNothing();
       var _ := me.InstanceUsesInvariant() + 2; //  error: same as above (this can be copied as much as you want)
     }
     x := 1;
  }
  
  // invariant assumed here
  function InstanceUsesInvariant(): int reads this {
    1 / x
  }
  
  // NB: invariant is not assumed/asserted in these
  static method MethodReadsNothing() reads {} {}
  opaque static predicate FunctionReadsNothing() reads {} { true }
 
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