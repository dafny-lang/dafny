// RUN: %testDafnyForEachResolver "%s"



function DecodeRecursively(s: seq<int>): (b: seq<int>) {
  seq(|s|, i requires 0 <= i < |s| =>
    var d := s[0]; // this line produced the reported error, prior to the fix
    s[i]
  )
}
