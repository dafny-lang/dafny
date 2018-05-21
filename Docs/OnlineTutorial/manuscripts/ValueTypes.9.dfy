function sorted2(s: seq<int>): bool
{
   0 < |s| ==> (forall i :: 0 < i < |s| ==> s[0] <= s[i]) &&
               sorted2(s[1..])
}