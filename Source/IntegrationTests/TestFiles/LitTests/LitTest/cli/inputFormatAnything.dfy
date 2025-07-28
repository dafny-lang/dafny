// RUN: %tobinary %s > %t.dbin
// RUN: %resolve --check-source-location-consistency --input-format Binary %S/Inputs/additional.dfy --allow-warnings --stdin < %t.dbin > %t
// RUN: %diff "%s.expect" "%t"

class Anything {
  const x := 3123.012314

  method foo() {
    while(true) {
      continue;
    }
    assert(old(this) == this);
    assert(unchanged(this));
    assert(fresh(this));
    var v := new Anything;
    assert(v is Anything);
    
    var tab := new int[3,4];
    tab[0,0] := 0;
    assert(tab[0,0] == 0);
    
  }
  
    
  function P2(x:int, y:int) : bool {
    x>y
  }
    
  function P(x:int) : bool {
    P2(x,10)
  }
}

trait ATrait {
}
