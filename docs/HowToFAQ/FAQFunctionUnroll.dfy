function LengthSum(s: seq<string>): nat {
  if |s| == 0 then 0
  else |s[0]| + LengthSum(s[1..])
}

lemma LengthSum1(s: seq<string>)
  requires |s| == 1
  ensures LengthSum(s) == |s[0]|
{
  // trivial
}

lemma LengthSum2(s: seq<string>)
  requires |s| == 2
  ensures LengthSum(s) == |s[0]| + |s[1]|
{
  // Doesn't work.  I need...
  LengthSum1(s[1..]);
}

lemma LengthSum3(s: seq<string>)
  requires |s| == 3
  ensures LengthSum(s) == |s[0]| + |s[1]| + |s[2]|
{
  // Doesn't work.  I need...
  LengthSum2(s[1..]);
}
