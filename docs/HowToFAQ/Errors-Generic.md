<!-- %default %useHeadings %check-ids -->

<!-- FILE ./DafnyCore/Generic/Util.cs -->

## **Warning: constructors no longer need 'this' to be listed in modifies clauses** {#p_deprecated_this_in_constructor_modifies_clause}

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

<!-- %check-resolve %options --unicode-chars=true -->
```dafny
char c := '\u0000';
```

When using the option `--unicode-chars=true` all unicode characters are written with `\\U`, not `\\`.

## **Error: \\U{X..X} escape sequence must have at most six hex digits** {#g_unicode_escape_must_have_six_digits}

<!-- %check-resolve %options --unicode-chars=true -->
```dafny
char c := '\U00AABBCC';
```

When using the option `--unicode-chars=true` all unicode characters are written with `\\U`, not `\\`.

## **Error: \\U{X..X} escape sequence must be less than 0x110000** {#g_unicode_escape_is_too_large}

<!-- %check-resolve %options --unicode-chars=true -->
```dafny
char c := '\U110011';
```

Unicode characters (with `--unicode-chars=true`) are defined only up through `0x110000`.

## **Error: \\U{X..X} escape sequence must be less than 0x110000** {#g_unicode_escape_may_not_be_surogate}

<!-- %check-resolve %options --unicode-chars=true -->
```dafny
char c := '\UD900';
```

The allowed range of unicode characters in Dafny excludes the surrogate characters in the range 0xD800 .. 0xE000.
<!-- TODO - need a reference -->

## **Error: \\U escape sequences are not permitted when Unicode chars are disabled** {#g_U_unicode_chars_are_disallowed}

<!-- %check-resolve %options --unicode-chars=false -->
```dafny
char c := '\UD000';
```

With `--unicode-chars=false`, all unicode characters are written with a lower-case `u`.


<!-- DafnyCore/Generic/Reporting.cs -->






<!-- TODO - not sure about this -->

## **Error: the included file _file_ contains error(s)** {#g_include_file_has_errors}

<!-- %no-check TODO - infrstructure does not handle examples with multiple errors -->
```dafny
include "testsource/TestA.dfy"
```

This error is shown when parsing a file A that includes another file B when B has errors of its own.
Without this message it can be easy to miss the fact that other errors in A are in fact caused
by errors in B. Some of the error messages shown may pertain to B rather than to A.
