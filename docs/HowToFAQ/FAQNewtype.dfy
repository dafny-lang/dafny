type int8 = x: int | -256 <= x < 256
newtype nint8 = x : int | -256 <= x < 256

method test(i: int, i8: int8, ni8: nint8) {
  var j: int, j8: int8, nj8: nint8;
  if -256 <= i < 256 { j8 := i; } // implicit conversion OK if in range
  if -256 <= i < 256 { nj8 := i as nint8; } // explicit conversion required
  j := i8; // always allowed
  j := ni8 as int; // explicit conversion required
}
  

