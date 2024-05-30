// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method ArrayInitEmpty<T>() {
    var a := new T[1];
}