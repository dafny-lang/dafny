// RUN: %exits-with 1 %baredafny resolve "%s" "%S/BadDoo.doo" 2> "%t"
// RUN: %diff "%s.expect" "%t"

// Input .doo file has invalid content

const c := 42
