function Sum(s: seq<int>): (result: int) {
  if |s| == 0 then
    0
  else
    Sum(s[0..|s|-1]) + s[|s| - 1]
    // We add the last element to the sum of the first
} by method {
  result := 0;
  for i := 0 to |s|
    invariant result == Sum(s[0..i])
  {
    assert s[0..i+1][0..i] == s[0..i];
     // Minimum hint needed for proof
    result := result + s[i];
  }
  assert s[0..|s|] == s;
} // One last hint