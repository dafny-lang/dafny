function Sum(s: seq<int>): (result: int) {
  if |s| == 0 then
    0
  else
    s[0] + Sum(s[1..])
} by method {
  result := 0; 
  for i := 0 to |s|
    invariant result == Sum(s[0..i])
    //        ^^^^^^^^^^^^^^^^^^^^^^
    //           Cannot be proved
  {
    result := result + s[i];
  }
  assert s[0..|s|] == s;
}