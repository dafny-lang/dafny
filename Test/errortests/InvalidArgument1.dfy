// RUN: rm -rf "%t"
// RUN: echo "-------" >> "%t"
// RUN: %exits-with 1  %dafny verify -- -- null.dfy
// RUN: echo "-------" >> "%t"
// RUN: %exits-with 1  %dafny verify -- --function-syntax:4 null.dfy
// RUN: echo "-------" >> "%t"
// RUN: %exits-with 1 %baredafny verify %args --function-syntax:2 null.dfy 2>> "%t"
// RUN: echo "-------" >> "%t"
// RUN: %exits-with 0 %baredafny verify %args --function-syntax:4 null.dfy 2>> "%t"
// RUN: echo "-------" >> "%t"
// RUN: %exits-with 1 %baredafny verify %args --quantifier-syntax:2 null.dfy 2>> "%t"
// RUN: echo "-------" >> "%t"
// RUN: %exits-with 1 %baredafny run %args  --relax-definite-assignment --enforce-determinism null.dfy 2>> "%t"
// RUN: %diff "%s.expect" "%t"
