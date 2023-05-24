// RUN: %exits-with 1 %baredafny resolve --use-basename-for-filename "%s" "%S/NoSuch.doo" 2> "%t"
// RUN: %diff "%s.expect" "%t"

// Input .doo file does not exist

const c := 42
