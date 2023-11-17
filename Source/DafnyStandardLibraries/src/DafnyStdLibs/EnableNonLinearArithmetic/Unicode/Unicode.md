## The `Unicode` module

This module defines concepts from the core specification
of the [Unicode Standard 15.1.0](https://www.unicode.org/versions/Unicode15.1.0/):
scalar values, code points, important kinds of code point sequences,
Unicode encoding forms and encoding schemes (including UTF-8 and UTF-16),
and helpful properties and functions for manipulation and conversion of Unicode strings.

At this time, the module can only be used with `--unicode-char:true`
(the default value since Dafny 4.0.0).
In the future, support for `--unicode-char:false` (via module abstraction/refinement)
will be added.
