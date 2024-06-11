// RUN: %exits-with 1 %baredafny resolve --use-basename-for-filename "%s" "%S/BadDoo.doo" > "%t"
// RUN: %diff "%s.expect" "%t"

// Input .doo file has invalid content

const c := 42
