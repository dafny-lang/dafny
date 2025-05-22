// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t".raw
// RUN: %exits-with 4 %baredafny verify %args --use-basename-for-filename=false --json-output "%s" >> "%t".raw
// RUN: %sed 's#%S##g' "%t".raw > "%t.raw2"
// In Windows, %S doesn't contain an additional prefix / that's in the URI.
// We want to replace with new Uri(%S).LocalPath but we don't have C# access here,
// as long as we're also supporting the original Lit
// RUN: %sed 's#////#///#g' "%t".raw2 > "%t.raw3"
// The "pos" field contains a different value on Windows and Linux (because of
// line ending differences), so we strip it out:
// RUN: %sed 's/"pos":[0-9]+,//g' "%t".raw3 > "%t"
// RUN: %diff "%s.expect" "%t"
newtype byte = i: int | 0 <= i < 256 // Info
static const x := 1 // Warning
const y: byte := 257 // Error

method M0() requires true requires false // Related location
method M1() { M0(); } // Error
