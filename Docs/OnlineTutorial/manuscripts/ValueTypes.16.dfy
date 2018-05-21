function update(s: seq<int>, i: int, v: int): seq<int>
   requires 0 <= index < |s|;
   ensures update(s, i, v) == s[i := v];
{
   s[..i] + [v] + s[i+1..]
   // This works by concatenating everything that doesn't
   // change with the singleton of the new value.
}