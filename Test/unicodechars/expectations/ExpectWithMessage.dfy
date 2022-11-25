// RUN: %dafny /compile:3 /compileTarget:cs /unicodeChar:1 "%s" > "%t" || true
// RUN: %dafny /compile:3 /compileTarget:go /unicodeChar:1 "%s" >> "%t" || true
// RUN: %dafny /compile:3 /compileTarget:java /unicodeChar:1 "%s" >> "%t" || true
// RUN: %dafny /compile:3 /compileTarget:js /unicodeChar:1 "%s" >> "%t" || true
// RUN: %dafny /compile:3 /compileTarget:py /unicodeChar:1 "%s" >> "%t" || true
// RUN: %diff "%s.expect" "%t"
include "../../expectations/ExpectWithMessage.dfy"
