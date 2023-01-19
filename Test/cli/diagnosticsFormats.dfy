// RUN: %exits-with 4 %dafny /compile:0 /diagnosticsFormat:text "%s" > "%t".raw
// RUN: %exits-with 4 %dafny /compile:0 /diagnosticsFormat:json "%s" >> "%t".raw
// RUN: %exits-with 4 %dafny /compile:0 /diagnosticsFormat:json -printTooltips "%s" >> "%t".raw
// RUN: %exits-with 4 %dafny /compile:0 /diagnosticsFormat:json -showSnippets:1 "%s" >> "%t".raw
// The "pos" field contains a different value on Windows and Linux (because of
// line ending differences), so we strip it out:
// RUN: %sed 's/"pos":[0-9]+,//g' "%t".raw > "%t"
// RUN: %diff "%s.expect" "%t"

newtype byte = i: int | 0 <= i < 256 // Info
static const x := 1; // Warning
const y: byte := 257; // Error

method M0() requires true requires false // Related location
method M1() { M0(); } // Error
