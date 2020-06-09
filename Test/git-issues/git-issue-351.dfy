// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


function method DecodeRecursively(s: seq<int>): (b: seq<int>) {
    seq(|s|, i requires 0 <= i < |s| =>
        var d := s[0]; // this line produces the error below
        s[i]
    )
}
