// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method test1() {
    var s := [1, 2, 3];
    var a := s[..]; // OK
    var b := s[0..2]; // OK
    var c := s[1..3]; // OK
    var d := s[1..1]; // OK
}
method test2() {
    var s := [1, 2, 3];
    var a := s[-1..]; // ERROR
}
method test3() {
    var s := [1, 2, 3];
    var a := s[4..]; // ERROR
}
method test3a() {
    var s := [1, 2, 3];
    var a := s[3..]; // OK
}
method test4() {
    var s := [1, 2, 3];
    var a := s[2..1]; // ERROR
}
method test5() {
    var s := [1, 2, 3];
    var a := s[..-1]; // ERROR
}
method test6() {
    var s := [1, 2, 3];
    var a := s[..4]; // ERROR
}
