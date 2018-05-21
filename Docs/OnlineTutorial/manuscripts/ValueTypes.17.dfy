method m()
{
   var a := new int[3]; // 3 element array of ints
   a[0], a[1], a[2] := 0, 3, -1;
   var s := a[..];
   assert s == [0, 3, -1];
}