// RUN: %dafny /arith:1 "%s" > "%t"
// RUN: %dafny /arith:2 "%s" >> "%t"
// RUN: %dafny /arith:3 "%s" >> "%t"
// RUN: %dafny /arith:4 "%s" >> "%t"
// RUN: %dafny /arith:5 "%s" >> "%t"
// RUN: %dafny /arith:6 "%s" >> "%t"
// RUN: %dafny /arith:7 "%s" >> "%t"
// RUN: %dafny /arith:8 "%s" >> "%t"
// RUN: %dafny /arith:9 "%s" >> "%t"
// RUN: %dafny /arith:10 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
    
}