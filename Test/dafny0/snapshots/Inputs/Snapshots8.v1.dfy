method M(x: int)
{
assert x < 20 || 10 <= x;  // always true
  
       assert x < 10;  // error
  Other(x);  // error: precondition violation
  assert x == 7;  // error: this is a new error in v1
}


       method Other(y: int)
         requires 0 <= y
       {
       }



method Posty() returns (z: int)
  ensures 2 <= z  // error: postcondition violation
{
  var t := 20;
  if t < z {
    assert true;  // this is a new assert
  } else {  // the postcondition violation occurs on this 'else' branch
  }
}

  method       NoChangeWhazzoeva(u: int)
  {
       assert u != 53;  // error
  }

method NoChangeAndCorrect() { assert true; }
