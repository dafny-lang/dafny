// RUN: %exits-with 2 %baredafny resolve --use-basename-for-filename --show-snippets:false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The #line should no longer be special
#line Q     
#zzzz


