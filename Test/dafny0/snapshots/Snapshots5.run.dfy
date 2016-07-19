// RUN: %dafny /compile:0 /verifySnapshots:2 /traceCaching:1 "%S/Inputs/Snapshots5.dfy" /autoTriggers:1 > "%t"
// RUN: %diff "%s.expect" "%t"
