// RUN: %baredafny build -t:rs "%s"
// RUN: "%S/avoid_soundness_mut-rust/cargo" run --release > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %baredafny translate rs --raw-pointers "%s"
// RUN: "%S/avoid_soundness_mut-rust/cargo" run --release > "%t"
// RUN: %diff "%s.expect" "%t"

newtype u8 = x: int | 0 <= x < 256

class X {
  var x: u8
  constructor() {
    x := 0;
  }
  
  method DoBoth(other: X)
    modifies this, other
  {
    this.x := 0;
    other.x := 1;
    if this.x == 1 {
      print "One\n";
    } else {
      print "Zero\n";
    }
  }
}

method Main() {
  var c := new X();
  c.DoBoth(c);
}