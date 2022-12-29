// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost method M() {
  var x :=
// In the following line, why are the range and term copied in Substitute?
//    var loo := 100; map y | 0 <= y < 100 :: y+1;
    var loo := 100; imap y: int | true :: 3;
}
