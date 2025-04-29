// RUN: %exits-with 1 %run --input foobar.dll "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
