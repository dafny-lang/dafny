method m()
{
   var a := new int[3]; // 3 element array of ints
   a[0], a[1], a[2] := 0, 3, -1;
   assert a[1..] == [3, -1];
   assert a[..1] == [0];
   assert a[1..2] == [3];
}