method Abs(x: int) returns (y: int)
   ensures 0 <= y;
{
   y := 0;
}
method Testing()
{
   var v := Abs(3);
   assert 0 <= v;
   assert v == 3;
}