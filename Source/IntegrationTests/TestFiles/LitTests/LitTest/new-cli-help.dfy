// RUN: %baredafny -h > "%t"
// RUN: %baredafny --help > "%t_X"
// RUN: %diff "%t" "%t_X"
