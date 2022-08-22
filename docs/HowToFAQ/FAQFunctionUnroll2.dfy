function LengthSum(s: seq<string>): nat {
  if |s| == 0 then 0
  else |s[0]| + LengthSum(s[1..])
}

function LengthSum_(s: seq<string>, n: nat): nat
  ensures LengthSum(s) == LengthSum_(s,n)
  ensures |s| > 0 && n > 0 ==> LengthSum_(s,n) == |s[0]| + LengthSum_(s[1..], n-1)
{
  if |s| == 0 || n == 0 then LengthSum(s)
              else |s[0]| + LengthSum_(s[1..], n-1)
}

lemma LengthSum1(s: seq<string>)
  requires |s| == 1
  ensures LengthSum(s) == |s[0]|
{
  // trivial
}

lemma LengthSum3(s: seq<string>)
  requires |s| == 3
  ensures LengthSum(s) == |s[0]| + |s[1]| + |s[2]|
{
  var _ := LengthSum_(s, 3);
}

lemma LengthSum9(s: seq<string>)
  requires |s| == 9
  ensures LengthSum(s) == |s[0]| + |s[1]| + |s[2]| + |s[3]| + |s[4]| + |s[5]| + |s[6]| + |s[7]| + |s[8]| 
{
  var _ := LengthSum_(s, 9);
}
