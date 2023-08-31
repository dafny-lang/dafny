// RUN: %exits-with 3 %dafny /compile:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method StatementsInCompiledMethod() {
  assume false;  // error
  calc {
    100;
  ==  { assume false; }  // error
    100;
  }
  assert true by {
    assume false;  // error
  }
  ghost var b := true;
  if b {
    assume false;  // error
  }
}

ghost method StatementsInGhostMethod() {
  // statements
  assume false;  // error
  calc {
    100;
  ==  { assume false; }  // error
    100;
  }
  assert true by {
    assume false;  // error
  }
  ghost var b := true;
  if b {
    assume false;  // error
  }
}

method ExpressionsInCompiledMethod() {
  var a :=
    assume false;  // error
    5;
  var b :=
    calc {
      100;
    ==  { assume false; }  // error
      100;
    }
    5;
  var c :=
    assert true by {
      assume false;  // error
    }
    5;
  var d :=
    ghost var g := 5;
    assume false;  // error
    5;

  ghost var x :=
    assume false;  // error
    5;
  ghost var y :=
    calc {
      100;
    ==  { assume false; }  // error
      100;
    }
    5;
  ghost var z :=
    assert true by {
      assume false;  // error
    }
    5;
  ghost var w :=
    ghost var g := 5;
    assume false;  // error
    5;
}

ghost method ExpressionsInGhostMethod() {
  var a :=
    assume false;  // error
    5;
  var b :=
    calc {
      100;
    ==  { assume false; }  // error
      100;
    }
    5;
  var c :=
    assert true by {
      assume false;  // error
    }
    5;
  var d :=
    ghost var g := 5;
    assume false;  // error
    5;

  ghost var x :=
    assume false;  // error
    5;
  ghost var y :=
    calc {
      100;
    ==  { assume false; }  // error
      100;
    }
    5;
  ghost var z :=
    assert true by {
      assume false;  // error
    }
    5;
  ghost var w :=
    ghost var g := 5;
    assume false;  // error
    5;
}

function CompiledFunction(): int {
  assume false;  // error
  calc {
    100;
  ==  { assume false; }  // error
    100;
  }
  assert true by {
    assume false;  // error
  }
  ghost var g := 5;
  assume false;  // error
  5
}

ghost function GhostFunction(): int {
  assume false;  // error
  calc {
    100;
  ==  { assume false; }  // error
    100;
  }
  assert true by {
    assume false;  // error
  }
  ghost var g := 5;
  assume false;  // error
  5
}

// --------------------------------------------------

method SpecificationOfCompiledMethod()
  requires assume false; true  // error
  modifies assume false; {}  // error
  ensures assume false; true  // error
  decreases assume false; 5  // error
{
}

ghost method SpecificationOfGhostMethod()
  requires assume false; true  // error
  modifies assume false; {}  // error
  ensures assume false; true  // error
  decreases assume false; 5  // error
{
}

function SpecificationOfCompiledFunction(): int
  requires assume false; true  // error
  reads assume false; {}  // error
  ensures assume false; true  // error
  decreases assume false; 5  // error
{
  5
}

ghost function SpecificationOfGhostFunction(): int
  requires assume false; true  // error
  reads assume false; {}  // error
  ensures assume false; true  // error
  decreases assume false; 5  // error
{
  5
}

method SpecificationOfCompiledMethodWithoutBody()  // error: has no body
  requires assume false; true  // error
  modifies assume false; {}  // error
  ensures assume false; true  // error
  decreases assume false; 5  // error

ghost method SpecificationOfGhostMethodWithoutBody()  // error: has no body
  requires assume false; true  // error
  modifies assume false; {}  // error
  ensures assume false; true  // error
  decreases assume false; 5  // error

function SpecificationOfCompiledFunctionWithoutBody(): int  // error: has no body
  requires assume false; true  // error
  reads assume false; {}  // error
  ensures assume false; true  // error
  decreases assume false; 5  // error

ghost function SpecificationOfGhostFunctionWithoutBody(): int  // error: has no body
  requires assume false; true  // error
  reads assume false; {}  // error
  ensures assume false; true  // error
  decreases assume false; 5  // error

// --------------------------------------------------

least predicate ExtremePredicate()
  requires assume false; true  // error
{
  assume false;  // error
  true
}

least lemma ExtremeLemma()
  requires assume false; true  // error
  ensures assume false; true  // error
  decreases assume false; 5  // error
{
  assume false;  // error
}

least predicate ExtremePredicateWithoutBody()  // error: has no body
  requires assume false; true  // error

least lemma ExtremeLemmaWithoutBody()  // error: has no body
  requires assume false; true  // error
  ensures assume false; true  // error
  decreases assume false; 5  // error

// --------------------------------------------------

newtype NewType = x | x % 2 == 1
  witness assume false; 5  // error

type SubsetType = x | x % 2 == 1
  witness assume false; 5  // error

newtype NewTypeGhostWitness = x | x % 2 == 1
  ghost witness assume false; 5  // error

type SubsetTypeGhostWitness = x | x % 2 == 1
  ghost witness assume false; 5  // error

const CompiledConst := assume false; 5  // error

ghost const GhostConst := assume false; 5  // error

class C {
  const InstanceCompiledConst := assume false; 5  // error
  ghost const InstanceGhostConst := assume false; 5  // error
}

datatype D = D {
  const InstanceCompiledConst := assume false; 5  // error
  ghost const InstanceGhostConst := assume false; 5  // error
}

newtype T = int {
  const InstanceCompiledConst := assume false; 5  // error
  ghost const InstanceGhostConst := assume false; 5  // error
}

// --------------------------------------------------

function F(x: int, ghost y: int): int { 5 }
ghost function G(x: int): int { 5 }
method M(x: int, ghost y: int) { }
lemma N(x: int) { }

datatype Dt = Dt(x: int, ghost y: int)

method CompiledMethodCaller() {
  var a := F(assume false; 5, assume false; 6);  // error (x2)
  ghost var b := G(assume false; 5);  // error
  M(assume false; 5, assume false; 6);  // error (x2)
  N(assume false; 5);  // error
  var d := Dt(assume false; 5, assume false; 6);  // error (x2)
  ghost var e := Dt(assume false; 5, assume false; 6);  // error (x2)
}

ghost method GhostMethodCaller() {
  var a := F(assume false; 5, assume false; 6);  // error (x2)
  ghost var b := G(assume false; 5);  // error
  N(assume false; 5);  // error
  var d := Dt(assume false; 5, assume false; 6);  // error (x2)
  ghost var e := Dt(assume false; 5, assume false; 6);  // error (x2)
}

function CompiledFunctionCaller(): int {
  var a := F(assume false; 5, assume false; 6);  // error (x2)
  ghost var b := G(assume false; 5);  // error
  N(assume false; 5);  // error
  var d := Dt(assume false; 5, assume false; 6);  // error (x2)
  ghost var e := Dt(assume false; 5, assume false; 6);  // error (x2)
  100
}

ghost function GhostFunctionCaller(): int {
  var a := F(assume false; 5, assume false; 6);  // error (x2)
  ghost var b := G(assume false; 5);  // error
  N(assume false; 5);  // error
  var d := Dt(assume false; 5, assume false; 6);  // error (x2)
  ghost var e := Dt(assume false; 5, assume false; 6);  // error (x2)
  100
}

class A {

  method StatementsInCompiledMethod() {
    assume false;  // error
    calc {
      100;
    ==  { assume false; }  // error
      100;
    }
    assert true by {
      assume false;  // error
    }
    ghost var b := true;
    if b {
      assume false;  // error
    }
  }

  ghost method StatementsInGhostMethod() {
    // statements
    assume false;  // error
    calc {
      100;
    ==  { assume false; }  // error
      100;
    }
    assert true by {
      assume false;  // error
    }
    ghost var b := true;
    if b {
      assume false;  // error
    }
  }

}
