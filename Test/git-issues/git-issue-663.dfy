// RUN: %dafny /compile:1 "%s" > "%t"
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

function method CompiledFunction(): int {
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

function GhostFunction(): int {
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
  requires assume false; true  // BOGUS: missing error
  modifies assume false; {}  // BOGUS: missing error
  ensures assume false; true  // BOGUS: missing error
  decreases assume false; 5  // BOGUS: missing error
{
}

ghost method SpecificationOfGhostMethod()
  requires assume false; true  // BOGUS: missing error
  modifies assume false; {}  // BOGUS: missing error
  ensures assume false; true  // BOGUS: missing error
  decreases assume false; 5  // BOGUS: missing error
{
}

function method SpecificationOfCompiledFunction(): int
  requires assume false; true  // BOGUS: missing error
  reads assume false; {}  // BOGUS: missing error
  ensures assume false; true  // BOGUS: missing error
  decreases assume false; 5  // BOGUS: missing error
{
  5
}

function SpecificationOfGhostFunction(): int
  requires assume false; true  // BOGUS: missing error
  reads assume false; {}  // BOGUS: missing error
  ensures assume false; true  // BOGUS: missing error
  decreases assume false; 5  // BOGUS: missing error
{
  5
}

method SpecificationOfCompiledMethodWithoutBody()  // error: has no body
  requires assume false; true  // BOGUS: missing error
  modifies assume false; {}  // BOGUS: missing error
  ensures assume false; true  // BOGUS: missing error
  decreases assume false; 5  // BOGUS: missing error

ghost method SpecificationOfGhostMethodWithoutBody()  // error: has no body
  requires assume false; true  // BOGUS: missing error
  modifies assume false; {}  // BOGUS: missing error
  ensures assume false; true  // BOGUS: missing error
  decreases assume false; 5  // BOGUS: missing error

function method SpecificationOfCompiledFunctionWithoutBody(): int  // error: has no body
  requires assume false; true  // BOGUS: missing error
  reads assume false; {}  // BOGUS: missing error
  ensures assume false; true  // BOGUS: missing error
  decreases assume false; 5  // BOGUS: missing error

function SpecificationOfGhostFunctionWithoutBody(): int  // error: has no body
  requires assume false; true  // BOGUS: missing error
  reads assume false; {}  // BOGUS: missing error
  ensures assume false; true  // BOGUS: missing error
  decreases assume false; 5  // BOGUS: missing error

// --------------------------------------------------
  
inductive predicate ExtremePredicate()
  requires assume false; true  // BOGUS: missing error
{
  assume false;  // error
  true
}

inductive lemma ExtremeLemma()
  requires assume false; true  // BOGUS: missing error
  ensures assume false; true  // BOGUS: missing error
  decreases assume false; 5  // BOGUS: missing error
{
  assume false;  // error
}

inductive predicate ExtremePredicateWithoutBody()  // error: has no body
  requires assume false; true  // BOGUS: missing error

inductive lemma ExtremeLemmaWithoutBody()  // error: has no body
  requires assume false; true  // BOGUS: missing error
  ensures assume false; true  // BOGUS: missing error
  decreases assume false; 5  // BOGUS: missing error

// --------------------------------------------------
  
newtype NewType = x | x % 2 == 1
  witness assume false; 5  // BOGUS: missing error
  
type SubsetType = x | x % 2 == 1
  witness assume false; 5  // BOGUS: missing error

newtype NewTypeGhostWitness = x | x % 2 == 1
  ghost witness assume false; 5  // BOGUS: missing error
  
type SubsetTypeGhostWitness = x | x % 2 == 1
  ghost witness assume false; 5  // BOGUS: missing error

const CompiledConst := assume false; 5  // BOGUS: missing error
 
ghost const GhostConst := assume false; 5  // error

class C {
  const InstanceCompiledConst := assume false; 5  // BOGUS: missing error
  ghost const InstanceGhostConst := assume false; 5  // error
}

datatype D = D {
  const InstanceCompiledConst := assume false; 5  // BOGUS: missing error
  ghost const InstanceGhostConst := assume false; 5  // error
}

newtype T = int {
  const InstanceCompiledConst := assume false; 5  // BOGUS: missing error
  ghost const InstanceGhostConst := assume false; 5  // error
}

// --------------------------------------------------
  
function method F(x: int, ghost y: int): int { 5 }
function G(x: int): int { 5 }
method M(x: int, ghost y: int) { }
ghost method N(x: int) { }

datatype Dt = Dt(x: int, ghost y: int)

method CompiledMethodCaller() {
  var a := F(assume false; 5, assume false; 6);  // BOGUS: missing error (x2)
  ghost var b := G(assume false; 5);  // error
  M(assume false; 5, assume false; 6);  // BOGUS: missing error (x2)
  N(assume false; 5);  // error
  var d := Dt(assume false; 5, assume false; 6);  // BOGUS: missing error (x2)
  ghost var e := Dt(assume false; 5, assume false; 6);  // error (x2)
}

ghost method GhostMethodCaller() {
  var a := F(assume false; 5, assume false; 6);  // error (x2)
  ghost var b := G(assume false; 5);  // error
  N(assume false; 5);  // error
  var d := Dt(assume false; 5, assume false; 6);  // error (x2)
  ghost var e := Dt(assume false; 5, assume false; 6);  // error (x2)
}

function method CompiledFunctionCaller(): int {
  var a := F(assume false; 5, assume false; 6);  // BOGUS: missing error (x2)
  ghost var b := G(assume false; 5);  // BOGUS: missing error
  N(assume false; 5);  // BOGUS: missing error
  var d := Dt(assume false; 5, assume false; 6);  // BOGUS: missing error (x2)
  ghost var e := Dt(assume false; 5, assume false; 6);  // BOGUS: missing error (x2)
  100
}

function GhostFunctionCaller(): int {
  var a := F(assume false; 5, assume false; 6);  // error (x2)
  ghost var b := G(assume false; 5);  // error
  N(assume false; 5);  // error
  var d := Dt(assume false; 5, assume false; 6);  // error (x2)
  ghost var e := Dt(assume false; 5, assume false; 6);  // error (x2)
  100
}
