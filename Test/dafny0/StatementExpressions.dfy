ghost method M(n: nat) //returns (y: nat)
{
  var y := F(n, 0);
}
function F(n: nat, p: int): nat
{
  calc {
    100;
  <  { if n != 0 { M(n-1); } }
    102;
  }
  n
}

ghost method MM(n: nat) returns (y: nat)
  decreases n, 0;
{
  if n != 0 {
    y := FF(n-1);
  }
}
function FF(n: nat): nat
  decreases n, 1;
{
  calc {
    100;
  <  { var y := MM(n); }
    102;
  }
  n
}

ghost method P(n: nat)
{
  if n != 0 {
    var y :=
      calc {
        12;
        { P(n-1); }
        12;
      }
      100;
    assert y == 100;
  }
}
ghost method Q(n: nat)
{
  if n != 0 {
    var y :=
      calc {
        12;
        { Q(n+1); }  // error: cannot prove termination
        12;
      }
      100;
    assert y == 102;  // error: assertion does not hold
  }
}
