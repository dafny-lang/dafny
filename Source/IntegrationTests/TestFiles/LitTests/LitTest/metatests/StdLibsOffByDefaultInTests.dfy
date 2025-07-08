
// RUN: %exits-with 2 %verify --allow-axioms "%s" > "%t"
// RUN: %verify --standard-libraries:true --allow-axioms "%s" >> "%t"
// RUN: %diff "%s.expect" "%t" 

module TriesToUseWrappers {

  import opened Std.Wrappers

  function SafeDiv(a: int, b: int): Option<int> {
    if b == 0 then None else Some(a/b)
  }
}
