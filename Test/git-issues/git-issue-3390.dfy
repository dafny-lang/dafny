// RUN: %exits-with 2 %baredafny resolve --use-basename-for-filename "%s" > "%t"


// This example gives a confusing error message

const z := 1 as bv4 | 1 as bv2 << 2
