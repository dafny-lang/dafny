function {:fuel 10} Sum(s: seq<nat>): nat {
  if |s| == 0 then 0
  else s[0] + Sum(s[1..])
}

lemma Sum1(s: seq<nat>)
  requires |s| == 1
  ensures Sum(s) == s[0]
{
  // trivial
}

lemma Sum2(s: seq<nat>)
  requires |s| == 2
  ensures Sum(s) == s[0] + s[1]
{
  // Doesn't work.  I need...
  // Sum1(s[1..]);
}

lemma Sum3(s: seq<nat>)
  requires |s| == 3
  ensures Sum(s) == s[0] + s[1] + s[2]
{
  // Doesn't work.  I need...
  // Sum2(s[1..]);
}
