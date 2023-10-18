
// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %verify --allow-standard-libraries:true "%s" >> "%t"
// RUN: %diff "%s.expect" "%t" 

module TriesToUseWrappers {

  import opened DafnyStdLibs.Wrappers

  function SafeDiv(a: int, b: int): Option<int> {
    if b == 0 then None else Some(a/b)
  }
<<<<<<< HEAD
<<<<<<< HEAD
=======
>>>>>>> 3ee79eaa9 (Add documentation and hook up check-examples)
}


// TODO:
// * Big ol README, especially regarding todos, standards, and brittleness
<<<<<<< HEAD
<<<<<<< HEAD
// * remove libraries submodule (confusing!)
=======
}
>>>>>>> fad95b0b9 (Off by default in tests)
=======
>>>>>>> 3ee79eaa9 (Add documentation and hook up check-examples)
=======
// * remove libraries submodule (confusing!)
>>>>>>> dbf2b404d (PR feedback)
