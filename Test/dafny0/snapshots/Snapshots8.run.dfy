// RUN: %dafny /compile:0 /verifySnapshots:3 /traceCaching:1 /errorTrace:0 Inputs/Snapshots8.dfy > "%t"
// RUN: %diff "%s.expect" "%t"
