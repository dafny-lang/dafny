// RUN: %exits-with 2 %baredafny run %args --target=cs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module FromBugReport {
  predicate P() { 
    // The following expression depends on the allocation state, so it should not be allowed
    // in a function.
    exists o: set<object> :: |o| > 10 // error: function body is not allowed to depend on allocation state
  }

  type SetOfObjects = set<object>

  predicate Q() {
    // The following expression is the same as the one in the body of P() above. Thus, an
    // error should be generated for it as well. (Previously, the type synonym had caused
    // no error to be generated, which was buggy.)
    exists o: SetOfObjects :: |o| > 10 // error: function body is not allowed to depend on allocation state
  }
}

module BadTypeCharacteristics {
  type Int(!new) = int
  type Reference(!new) = object // error: type is not !new
  type IntX(!new)<X> = int
  type ReferenceX(!new)<X> = object // error: type is not !new

  type ParamX(!new)<X> = X // error: type is not !new
  type GoodParamX(!new)<X(!new)> = X

  datatype Dt<X(!new), Y> = Dt(X, Y)
  type Dt0(!new) = Dt<int, int>
  type Dt1(!new) = Dt<object, int> // error (x2): type parameter 0 is not allowed to contain references; Dt1 contains references
  type Dt2(!new) = Dt<int, object> // error: Dt2 contains references
  type Dt3(!new) = Dt<object, object> // error (x2): type parameter 0 is not allowed to contain references; Dt3 contains references

  datatype Et<X, Y> = Et(X, Y)
  type Et0(!new) = Et<int, int>
  type Et1(!new) = Et<object, int> // error: Et1 contains references
  type Et2(!new) = Et<int, object> // error: Et2 contains references
  type Et3(!new) = Et<object, object> // error: Et3 contains references

  datatype Ft<X, Y> = Ft(int, Y)
  type Ft0(!new) = Ft<int, int>
  type Ft1(!new) = Ft<object, int> // error: Ft1 contains references
  type Ft2(!new) = Ft<int, object> // error: Ft2 contains references
  type Ft3(!new) = Ft<object, object> // error: Ft3 contains references

  type FuncA(!new) = bool -> bool
  type FuncB(!new) = object -> bool // error: FuncB contains references
  type FuncC(!new) = bool -> object // error: FuncC contains references
  type FuncD(!new) = object -> object // error: FuncD contains references
  type FuncE(!new) = (int, int, object) -> bool // error: FuncE contains references

  type Opaque
  type OpaqueReferenceFree(!new)
  type Opaq0(!new) = Opaque // error: Opaq0 contains references
  type Opaq1(!new) = OpaqueReferenceFree

  type TypeParam0(!new)<X, Y> = X // error: TypeParam0 contains references
  type TypeParam1(!new)<X(!new), Y> = X

  type ObjectSyn0 = object
  type ObjectSyn1 = ObjectSyn0
  type ObjectSyn2 = ObjectSyn1
  type ObjectSyn3(!new) = ObjectSyn2 // error: ObjectSyn3 contains references

  type IntSyn0 = int
  type IntSyn1 = IntSyn0
  type IntSyn2 = IntSyn1
  type IntSyn3(!new) = IntSyn2
}

module A {
  export Everything
    reveals *
  export Limited
    provides *

  type Int = int
  type Reference = object
  type IntX<X> = int
  type ReferenceX<X> = object
  type Param<X> = X
}

module B {
  import A`Everything

  predicate F() {
    exists o: A.Int :: o == o
  }

  predicate G() {
    exists o: A.Reference :: o == o // error: function body is not allowed to depend on allocation state
  }

  predicate H0() {
    exists o: A.IntX<int> :: o == o
  }

  predicate H1() {
    exists o: A.IntX<object> :: o == o
  }

  predicate I0() {
    exists o: A.ReferenceX<int> :: o == o // error: function body is not allowed to depend on allocation state
  }

  predicate I1() {
    exists o: A.ReferenceX<object> :: o == o // error: function body is not allowed to depend on allocation state
  }

  predicate J0() {
    exists o: A.Param<int> :: o == o
  }

  predicate J1() {
    exists o: A.Param<object> :: o == o // error: function body is not allowed to depend on allocation state
  }
}

module C {
  import A`Limited

  predicate F() {
    exists o: A.Int :: o == o // error: function body is not allowed to depend on allocation state
  }

  predicate G() {
    exists o: A.Reference :: o == o // error: function body is not allowed to depend on allocation state
  }

  predicate H0() {
    exists o: A.IntX<int> :: o == o // error: function body is not allowed to depend on allocation state
  }

  predicate H1() {
    exists o: A.IntX<object> :: o == o // error: function body is not allowed to depend on allocation state
  }

  predicate I0() {
    exists o: A.ReferenceX<int> :: o == o // error: function body is not allowed to depend on allocation state
  }

  predicate I1() {
    exists o: A.ReferenceX<object> :: o == o // error: function body is not allowed to depend on allocation state
  }

  predicate J0() {
    exists o: A.Param<int> :: o == o // error: function body is not allowed to depend on allocation state
  }

  predicate J1() {
    exists o: A.Param<object> :: o == o // error: function body is not allowed to depend on allocation state
  }
}

module AA {
  export Limited
    provides *

  type Int(!new) = int
  type IntX(!new)<X> = int
  type Param(!new)<X(!new)> = X
}

module D {
  import A = AA`Limited

  predicate F() {
    exists o: A.Int :: o == o
  }

  predicate H0() {
    exists o: A.IntX<int> :: o == o
  }

  predicate H1() {
    exists o: A.IntX<object> :: o == o
  }

  predicate J0() {
    exists o: A.Param<int> :: o == o
  }

  predicate J1() {
    exists o: A.Param<object> :: o == o // error: function body is not allowed to depend on allocation state
  }
}

module DatatypeSet {
  datatype Obs = Obs(s: set<object>)

  predicate LotsOfObjects() {
    exists o: Obs :: |o.s| > 10 // error: function body is not allowed to depend on allocation state
  }
}

module Datatypes {
  class C {}
  datatype D = DC(c: C)
  type X(!new) = D // error: RHS contains references

  datatype M<X> = MA | MB(bv8) | MC(array2<real>) | MD(X)
  type SM0(!new) = M<int> // error: RHS contains references
  type SM1(!new) = M<object> // error: RHS contains references

  datatype N<X> = NothingToSee(int)
  type SN0(!new) = N<int>
  type SN1(!new) = N<object> // error: RHS contains references (it matters not that the type argument is not used by N)
}

module DatatypeWithMembers {
  datatype Datatype<X(!new), Y> = Ctor(X, Y)
  {
    method Test() {
      NoReferencesPlease<X>();
      NoReferencesPlease<Y>(); // error: Y may contain references
      NoReferencesPlease<object>(); // error: type argument contains references
    }

    function ApplyToXSet(S: set<X>, f: X ~> X): set<X>
      requires forall x :: x in S ==> f.reads(x) == {} && f.requires(x)

    function ApplyToYSet(S: set<Y>, f: Y ~> Y): set<Y>
      requires forall y :: y in S ==> f.reads(y) == {} && f.requires(y)
  }

  method NoReferencesPlease<X(!new)>() {
  }

  function ApplyToSetNoReferences<X(!new)>(S: set<X>, f: X ~> X): set<X>
    requires forall x :: x in S ==> f.reads(x) == {} && f.requires(x)

  function ApplyToSet<Y>(S: set<Y>, f: Y ~> Y): set<Y>
    requires forall y :: y in S ==> f.reads(y) == {} && f.requires(y)
}

module DatatypeExporter {
  export Revealer
    reveals M, N
  export Provider
    provides M, N

  datatype M<X> = MA | MB(bv8) | MC(array2<real>) | MD(X)
  datatype N<X> = NothingToSee(int)
}

module DatatypeImporter0 {
  import I = DatatypeExporter`Revealer

  type SM0(!new) = I.M<int> // error: RHS contains references
  type SM1(!new) = I.M<object> // error: RHS contains references

  type SN0(!new) = I.N<int>
  type SN1(!new) = I.N<object> // error: RHS contains references
}

module DatatypeImporter1 {
  import I = DatatypeExporter`Provider

  type SM0(!new) = I.M<int> // error: RHS may contain references
  type SM1(!new) = I.M<object> // error: RHS may contain references
  type SN0(!new) = I.N<int> // error: RHS may contain references
  type SN1(!new) = I.N<object> // error: RHS may contain references
}
