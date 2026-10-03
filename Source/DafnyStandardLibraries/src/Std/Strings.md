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

`DecimalConversion` and `HexConversion` provide corresponding
`LemmaNatRoundTrip` and `LemmaIntRoundTrip` lemmas. The hexadecimal signed
lemma takes a sign character that must not occur in `charToDigit`.
Decimal conversion uses `'-'`.

These lemmas recover the original number, not necessarily an original input
string. Parsing accepts leading zeros and hexadecimal lowercase aliases,
whereas formatting emits canonical digits: for example, hexadecimal `"00ab"`
formats back to `"AB"`, and decimal `"-0"` formats back to `"0"`.

## Custom digit alphabets

Refinements of `ParametricConversion` can use `LemmaOfDigitsToNat`,
`LemmaOfNatToNat`, and `LemmaOfIntToInt` after establishing
`DigitCharsConsistent()`. This predicate requires each canonical digit
character to decode to its own index:
`charToDigit[chars[d]] == d` for every valid index `d`, with the map lookup
defined. Extra recognized aliases are allowed.

The existing `CharsConsistent` lemma proves the opposite composition and
does not rule out repeated canonical characters. For example,
`chars == "00"` and `charToDigit == map['0' := 0]` satisfy that older law,
but formatting and parsing `1` yields `0`. The new law is an explicit premise
on the new generic lemmas, so existing refinements remain compatible.
The signed generic lemma additionally requires its sign character not to
occur in `charToDigit`.

`LemmaOfDigitsToNat` handles the little-endian digit sequences used by
`Arithmetic.LittleEndianNat`, including empty sequences and high-order zeros.
Its numeric result is `ToNatRight(digits)`. See
[`StringsExamples.dfy`](../../examples/StringsExamples.dfy) for a binary
refinement and executable round-trip examples.
