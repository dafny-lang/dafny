// RUN: %exits-with 1 %baredafny build -t:lib  --use-basename-for-filename "%s" --output: 2> "%t"
// RUN: %diff "%s.expect" "%t"

// Missing output

const c := 42
