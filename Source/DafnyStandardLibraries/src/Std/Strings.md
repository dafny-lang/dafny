## The `Strings` module

This module provides several common utilities for manipulating strings,
in particular converting values of common types such as `bool`, `nat`, and `int`
to and from their string representations.

Note that since in Dafny `string` is just an alias for `seq<char>`,
many common string operations are available in the 
[`Collections.Seqs` module](../Collections.md) instead.
The `Strings` module only provides utilities more specific to sequences of characters.
