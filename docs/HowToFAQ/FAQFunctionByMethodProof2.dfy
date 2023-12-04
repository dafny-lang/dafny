function Sum(s: seq<int>): (result: int) {
  if |s| == 0 then
    0
  else
    s[0] + Sum(s[1..])
} by method {
  result := 0;
  for i := 0 to |s|
    invariant result + Sum(s[i..]) == Sum(s) // New invariant
  {
    result := result + s[i];
  }
} // No hint needed at the end

lemma IntermediateProperty(result: int, result': int, i: int, s: seq<int>)
  requires 0 <= i < |s|
  requires result' == result + s[i]
  requires result + Sum(s[i..]) == Sum(s)
  ensures result' + Sum(s[i+1..]) == Sum(s)
{
  calc {
     Sum(s);
  == result + Sum(s[i..]);             // Requires definition
  == result + (s[i]  + Sum(s[i+1..])); // Definition of Sum()
  ==(result +  s[i]) + Sum(s[i+1..]);  // Associativity
  == result'         + Sum(s[i+1..]);  // Definition of result'
  }
}