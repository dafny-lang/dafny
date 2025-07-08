// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method IndicesInDomain() {
    var a1 := new int[1](i requires i > 0 => 1);
    var a2 := new int[1, 1]((i, j) requires i > 0 && j < 0 => 1);
    var s := seq(1, i requires i > 0 => 1);
}