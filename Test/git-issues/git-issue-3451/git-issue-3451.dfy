// RUN: %exits-with 2 %baredafny resolve --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The #line should no longer be special
const s := @"
#line 5     
"
const k = 6  // error


