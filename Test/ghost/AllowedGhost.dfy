// RUN: %dafny /compile:0 /dprint:- "%s" /env:0 > "%t"
// RUN: %diff "%s.expect" "%t"

method Test()
{
    // Tuples with a single ghost component are allowed and they are compiled to empty tuples.
    var x := (ghost 123);
    var (y) := (ghost 123);
    ghost var z: (ghost int) := (ghost 123);
}
