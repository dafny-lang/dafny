Strings and Characters
======================

* char
  * With --unicode-char
    * Represented with something that can cover all 21 bits of Unicode space
    * C#: Rune
    * Java: int + CodePoint
    * Javascript: CodePoint (wrapping `number`)
    * Python: CodePoint (wrapping `str` of length one)
    * Go: CodePoint (wrapping `rune`)
  * Without --unicode-char
    * 
* utilities
  * Several cloned methods like Seq.[Unicode]FromString, CharMethodQualifier() used to distinguish in compilers
* print
  * With --unicode-char
    * direct statically-known string printed verbatim (TODO: verbatim not a great name?)
    * indirect statically-known string printed verbatim with quotes
    * `Sequence<T>` type for `seq<E>` has some flavour of "ToVerbatimString", 
      only safe to call if `E` is `char` and --unicode-char is on
      (so `T` is the runtime's code point type)
    * chars always printed with escapes, single quotes
  * Without --unicode-char
    * Depends on the backend
* Readability
  * Character and string literals are still translated to literals in the target language as much as possible.
    Such values are helpful as landmarks when trying to understand the compiled code.
  * MightContainNonAsciiCharacters as conservative guard.