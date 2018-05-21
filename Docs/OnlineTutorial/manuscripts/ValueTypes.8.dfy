function sorted(s: seq<int>): bool
{
   forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}