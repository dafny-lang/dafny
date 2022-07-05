// RUN: %dafny_0 /compile:0 /diagnosticsFormat:text "%s" > "%t"
// RUN: %dafny_0 /compile:0 /diagnosticsFormat:json "%s" >> "%t"
// RUN: %dafny_0 /compile:0 /diagnosticsFormat:text -printTooltips "%s" >> "%t"
// RUN: %dafny_0 /compile:0 /diagnosticsFormat:json -printTooltips "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

newtype byte = i: int | 0 <= i < 256 // Info
static const x := 1; // Warning
const y: byte := 257; // Error

method M0() requires true requires false // Related location
method M1() { M0(); } // Error
