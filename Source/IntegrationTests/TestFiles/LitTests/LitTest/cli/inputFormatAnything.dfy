// RUN: %tobinary %s > %t.assertFalse.dbin
// RUN: %resolve --check-source-location-consistency --input-format Binary %S/Inputs/additional.dfy --allow-warnings --stdin < %t.assertFalse.dbin > %t
// RUN: ! %resolve --check-source-location-consistency --input-format Binary --allow-warnings --stdin < %S/Inputs/inputFormat.incorrectSourceLocation.dbin >> %t
// RUN: %diff "%s.expect" "%t"

class Anything {
  const x := 3123.012314

  function bar(x:int, y:int):int {
    x+y
  }

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
    
    var tmp := bar(0,1);
  }
}

trait ATrait {
}
