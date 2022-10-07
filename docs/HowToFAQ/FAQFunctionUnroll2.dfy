function Sum(s: seq<nat>): nat {
  if |s| == 0 then 0
  else s[0] + Sum(s[1..])
}

function Sum_(s: seq<nat>, n: nat): nat
  ensures Sum(s) == Sum_(s,n)
  ensures |s| > 0 && n > 0 ==> Sum_(s,n) == s[0] + Sum_(s[1..], n-1)
{
  if |s| == 0 || n == 0 then Sum(s)
  else s[0] + Sum_(s[1..], n-1)
}

lemma Sum1(s: seq<nat>)
  requires |s| == 1
  ensures Sum(s) == s[0]
{
  // trivial
}

lemma Sum3(s: seq<nat>)
  requires |s| == 3
  ensures Sum(s) == s[0] + s[1] + s[2]
{
  var _ := Sum_(s, 3);
}

lemma Sum9(s: seq<nat>)
  requires |s| == 9
  ensures Sum(s) == s[0] + s[1] + s[2] + s[3] + s[4] + s[5] + s[6] + s[7] + s[8]
{
  var _ := Sum_(s, 9);
}
