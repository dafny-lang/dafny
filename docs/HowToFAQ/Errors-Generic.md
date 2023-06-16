<!-- %default %useHeadings %check-ids -->

<!-- FILE ./DafnyCore/Generic/Util.cs -->

## **Warning: constructors no longer need 'this' to be listed in modifies clauses** {#g_deprecated_this_in_constructor_modifies_clause}

<!-- %check-resolve-warn -->
```dafny
class A {
  constructor () modifies this {}
}
```

The purpose of a constructor is to initialize a newly allocated instance of a class.
Hence it always modifies the `this` object.
Previously it was required to list `this` in the modifies clause of the
constructor to specify this property, but now `this` is always implicitly 
a part of the modifies clause. 
If the constructor only modifies its own object (as is the very common case)
then no explicit modifies clause is needed at all.

<!-- TODO - 2 instances -- needs an example using set display-->

## **Error: \\u escape sequences are not permitted when Unicode chars are enabled** {#g_no_old_unicode_char}

<!-- %check-resolve %options --unicode-char=true -->
```dafny
const c := '\u0000'
```

When using the option `--unicode-chars=true` all unicode characters are written with `\\U`, not `\\`.

## **Error: \\U{X..X} escape sequence must have at most six hex digits** {#g_unicode_escape_must_have_six_digits}

<!-- %check-resolve %options --unicode-char=true -->
```dafny
const c := '\U{00AABBCC}'
```

When using the option `--unicode-chars=true` all unicode characters are written with `\\U`, not `\\`.

## **Error: \\U{X..X} escape sequence must be less than 0x110000** {#g_unicode_escape_is_too_large}

<!-- %check-resolve %options --unicode-char=true -->
```dafny
const c := '\U{110011}'
```

Unicode characters (with `--unicode-chars=true`) are defined only up through `0x110000`.

## **Error: \\U{X..X} escape sequence must not be a surrogate** {#g_unicode_escape_may_not_be_surrogate}

<!-- %check-resolve %options --unicode-char=true -->
```dafny
const c := '\U{D900}'
```

The allowed range of unicode characters in Dafny excludes the surrogate characters in the range 0xD800 .. 0xE000.

## **Error: \\U escape sequences are not permitted when Unicode chars are disabled** {#g_U_unicode_chars_are_disallowed}

<!-- %check-resolve %options --unicode-char=false -->
```dafny
const c := '\U{D000}'
```

With `--unicode-chars=false`, all unicode characters are written with a lower-case `u`.


<!-- FILE DafnyCore/DafnyOptions.cs -->

## **Error: Option _name_ unrecognized or unsupported in ':options' attributes.** {#g_option_error}

<!-- %check-resolve -->
```dafny
module {:options "ZZZ"} M {}
```

Dafny allows certain attributes to be defined for specific scopes (such as modules) in a program.
Only a small set of attributes are permitted to be locally redefined.
The error message is indicating that the given attribute is not one of them.
Note that some attributes (e.g. `--unicode-char`) must be consistent across the whole program.


