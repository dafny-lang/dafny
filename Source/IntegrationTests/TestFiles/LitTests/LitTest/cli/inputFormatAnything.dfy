// RUN: %tobinary %s > %t.assertFalse.dbin
// RUN: %resolve --input-format Binary %S/Inputs/additional.dfy --allow-warnings --stdin < %t.assertFalse.dbin > %t
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
}

trait ATrait {
}
