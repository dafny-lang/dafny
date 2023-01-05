// RUN: %exits-with 1 %baredafny foobar.dll "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method IrrelevantStartsOnlyFakeFoobarDll() {}