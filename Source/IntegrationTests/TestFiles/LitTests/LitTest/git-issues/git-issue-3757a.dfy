// RUN: %exits-with 2 %baredafny resolve --show-snippets:false --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const +
