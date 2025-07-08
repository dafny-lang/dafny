// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s" -- --unicode-char=false


// Ensuring that the special support for surrogate pairs in character literals
// doesn't allow character literals with multiple Unicode scalar values
// (which is a real danger given the complexity in allowing ' characters in identifiers).

module UnicodeCharSupport {
  const goodLiteral := '$'
  const goodNonASCIILiteral := '€'
  const badNonBMPLiteral := '💰' // error: too many characters in character literal
}
