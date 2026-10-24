# The `Strings` module

This module provides several common utilities for manipulating strings,
in particular converting values of common types such as `bool`, `nat`, and `int`
to and from their string representations.

Note that since in Dafny `string` is just an alias for `seq<char>`,
many common string operations are available in the
[`Collections.Seqs` module](../Collections.md) instead.
The `Strings` module only provides utilities more specific to sequences of characters.

## Number round trips

`LemmaNatRoundTrip(n)` proves `ToNat(OfNat(n)) == n` for every natural number,
and `LemmaIntRoundTrip(i)` proves `ToInt(OfInt(i)) == i` for every integer.
They also establish the preconditions needed to parse the generated strings.
For example:

<!-- %check-verify -->
```dafny
module NumberRoundTrips {
  import opened Std.Strings

  lemma Example(n: nat, i: int) {
    LemmaNatRoundTrip(n);
    assert ToNat(OfNat(n)) == n;
    LemmaIntRoundTrip(i);
    assert ToInt(OfInt(i)) == i;
  }
}
```

`DecimalConversion` and `HexConversion` have the same lemmas. Other refinements of `ParametricConversion`
get them as `LemmaOfNatToNat` and `LemmaOfIntToInt` by proving `DigitCharsConsistent()`, which, unlike
`CharsConsistent`, rules out repeated `chars`.
