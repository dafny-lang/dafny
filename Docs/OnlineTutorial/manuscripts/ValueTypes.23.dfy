method test() {
  var m := map[3 := 5, 4 := 6, 1 := 4];
  var l := map i | i in m && i != 3 :: m[i];
  assert l == map[4:= 6, 1 := 4];
}