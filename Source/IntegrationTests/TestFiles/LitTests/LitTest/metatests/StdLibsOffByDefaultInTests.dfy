
// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %verify --standard-libraries:true "%s" >> "%t"
// RUN: %diff "%s.expect" "%t" 

module TriesToUseWrappers {

  import opened DafnyStdLibs.Wrappers

  function SafeDiv(a: int, b: int): Option<int> {
    if b == 0 then None else Some(a/b)
  }
}


// TODO:
// * Big ol README, especially regarding todos, standards, and brittleness
// * remove libraries submodule (confusing!)
