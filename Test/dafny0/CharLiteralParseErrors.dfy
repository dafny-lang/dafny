// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Ensuring that the special support for surrogate pairs in character literals
// doesn't allow character literals with multiple Unicode scalar values
// (which is a real danger given the complexity in allowing ' characters in identifiers).

module UnicodeCharSupport {
  const goodLiteral := '$'
  const goodNonASCIILiteral := '€'
  const badNonBMPLiteral := '💰' // error: too many characters in character literal
}
