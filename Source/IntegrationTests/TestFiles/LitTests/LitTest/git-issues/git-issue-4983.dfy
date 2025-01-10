// RUN: %testDafnyForEachResolver --expect-exit-code=2 --refresh-exit-code=0 "%s" -- --general-traits:datatype

trait Parent {}

datatype Dt extends Parent = Dt {
  function GetParent(): Parent {
    // The implicit conversion in the following line once caused malformed Boogie to be generated
    this // error (in the legacy resolver): legacy resolver does not understand subtyping relationship with Parent
  }
}

function GetDtAsParent(): Parent {
  // The implicit conversion in the following line once caused malformed Boogie to be generated
  Dt // error (in the legacy resolver): legacy resolver does not understand subtyping relationship with Parent
}

type Abstract extends Parent {
  function GetParent(): Parent {
    this // error (in the legacy resolver): legacy resolver does not understand subtyping relationship with Parent
  }
}

function GetAbstract(): Abstract

function GetAbstractAsParent(): Parent {
  GetAbstract() // error (in the legacy resolver): legacy resolver does not understand subtyping relationship with Parent
}
