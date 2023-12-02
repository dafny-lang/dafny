include "defines-foo.dfy"

method bar() returns (x: int) {
    var temp := foo();
    x := temp + 2;
}