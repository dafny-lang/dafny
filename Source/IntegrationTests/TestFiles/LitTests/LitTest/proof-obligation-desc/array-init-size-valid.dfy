// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method ArrayInitSizeValid() {
    var a := new int[1] [];
}
