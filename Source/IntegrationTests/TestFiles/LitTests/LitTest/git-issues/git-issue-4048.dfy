// RUN: %exits-with 1 %baredafny build -t:lib --use-basename-for-filename "%s" x.doo > "%t"
// RUN: %diff "%s.expect" "%t"

// Tests case in which an input .doo file does not exist
const c := 5


