// RUN: %dafny  /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const one:int := 1;
const two:int := 2.5;   // error: type does not match
const three:int := 3;
const four:int := three + one;
const five:int := six - one;  // error: cycle five -> six
const six: int := five + one;
