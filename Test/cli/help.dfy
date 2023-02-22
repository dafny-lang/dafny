// RUN: %baredafny verify --toolchain-debugging-help > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: --rprint <file>
