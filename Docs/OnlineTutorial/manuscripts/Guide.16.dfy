method Abs(x: int) returns (y: int)
   ensures 0 <= y;
{
   y := 0;
}
method Testing()
{
   var v := Abs(3);
   assert 0 <= v;
   // this stil does not verify, but now it is actually not true:
   assert v == 3;
}