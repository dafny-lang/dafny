// RUN: %exits-with 1 %baredafny build -t:lib "%s" --output: 2> "%t"
// RUN: %diff "%s.expect" "%t"

// Missing output

const c := 42
