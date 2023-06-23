// RUN: %exits-with 2 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /unicodeChar:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module UnicodeCharSupport {
  const goodUnicodeEscape := '\U{10FFFF}'
  const badTooLongUnicodeEscape := '\U{1234567}' // error: \U{X..X} escape sequence must have at most six hex digits
  const badOutOfRangeUnicodeEscape := '\U{110000}' // error: \U{X..X} escape sequence must be at most 10FFFF
  const badSurrogateUnicodeEscape := '\U{D800}' // error: \U{X..X} escape sequence must not be a surrogate

  const goodLiteral := '$'
  const goodNonASCIILiteral := '€'
  const goodNonBMPLiteral := '💰'
  // Ensuring that the special support for surrogate pairs in character literals
  // doesn't allow character literals with multiple Unicode scalar values
  // (which is a real danger given the complexity in allowing ' characters in identifiers).
  const badMultiCharLiteral := '€€' // error: invalid NameSegment
}
