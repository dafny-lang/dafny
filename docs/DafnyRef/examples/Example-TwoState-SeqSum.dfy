function SeqSum(s: seq<Cell>): int
  reads s
{
  if s == [] then 0 else s[0].data + SeqSum(s[1..])
}

twostate lemma IncSumDiff(s: seq<Cell>)
  requires forall c :: c in s ==> Increasing(c)
  ensures old(SeqSum(s)) <= SeqSum(s)
{
  if s == [] {
  } else {
    calc {
      old(SeqSum(s));
    ==  // def. SeqSum
      old(s[0].data + SeqSum(s[1..]));
    ==  // distribute old
      old(s[0].data) + old(SeqSum(s[1..]));
    <=  { assert Increasing(s[0]); }
      s[0].data + old(SeqSum(s[1..]));
    <=  { IncSumDiff(s[1..]); }
      s[0].data + SeqSum(s[1..]);
    ==  // def. SeqSum
      SeqSum(s);
    }
  }
}
