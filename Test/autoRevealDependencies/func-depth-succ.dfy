// RUN: %baredafny verify %args --default-function-opacity autoRevealDependencies "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function f() : bool { true }
function g() : bool { f() }
function h() : bool { g() }
function i() : bool { h() }

function {:autoRevealDependencies 4} p() : (r: bool)
  ensures r
{ 
  i() 
}
