function Sum(s: seq<int>): (result: int) {
  if |s| == 0 then 0 else s[0] + Sum(s[1..])
} by method {
  result := 0;
  for i := |s| downto 0              // Reverse. First i == |s| - 1
    invariant result == Sum(s[i..])  // The invariant looks like the function
  {
    result := s[i] + result;         // Note how we sum in reverse as well.
  }
} // No hint needed at the end