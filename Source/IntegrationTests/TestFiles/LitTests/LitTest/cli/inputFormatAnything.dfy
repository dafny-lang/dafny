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
    
    var tab := new int[3,4];
    assert(tab.Length0==3);
    assert(tab.Length1==4);
  }
}

trait ATrait {
}