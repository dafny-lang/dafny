// RUN: %dafny /compile:0 /verifySnapshots:2 /traceCaching:1 "%S/Inputs/Snapshots7.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"
