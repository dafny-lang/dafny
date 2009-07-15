class Termination {
  method A(N: int)
    requires 0 <= N;
  {
    var i := 0;
    while (i < N)
      invariant i <= N;
      decreases N - i;
    {
      i := i + 1;
    }
  }

  method B(N: int)
    requires 0 <= N;
  {
    var i := N;
    while (true)
      invariant 0 <= i;
      decreases i;
    {
      i := i - 1;
      if (!(0 <= i)) {
        break;
      }
    }
    assert i == -1;
  }

  method Lex() {
    var x: int, y: int;
    call x := Update();
    call y := Update();
    while (!(x == 0 && y == 0))
      invariant 0 <= x && 0 <= y;
      decreases x, y;
    {
      if (0 < y) {
        y := y - 1;
      } else {
        x := x - 1;
        call y := Update();
      }
    }
  }

  method Update() returns (r: int)
    ensures 0 <= r;
  {
    r := 8;
  }

  method M() {
    var b := true;
    var i := 500;
    var r := new Termination;
    var s := {12, 200};
    var q := [5, 8, 13];
    while (true)
      decreases b, i, r;
//      invariant b ==> 0 <= i;
      decreases s, q;
    {
      if (12 in s) {
        s := s - {12};
      } else if (b) {
        b := !b;
        i := i + 1;
      } else if (20 <= i) {
        i := i - 20;
      } else if (r != null) {
        r := null;
      } else if (|q| != 0) {
        q := q[1..];
      } else {
        break;
      }
    }
  }
}
