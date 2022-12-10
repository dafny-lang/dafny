// RUN: %exits-with 4 %dafny /compile:0 /verifySnapshots:2 /traceCaching:1 %S/Inputs/Snapshots2.dfy > "%t"
// RUN: %diff "%s.expect" "%t"
