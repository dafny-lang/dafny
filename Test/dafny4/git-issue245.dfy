// RUN: %exits-with 4 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Issue 245 pointed out that trait override checks ignored the optional name of function results

trait T {
  // d does not name the result in either trait or class
  function method d(x: nat): nat
    ensures d(x) < 10 + x
  // f names the result in both trait and class
  function method f(x: nat): (res: nat)
    ensures res < 10 + x
  // g names the result in just the class
  function method g(x: nat): nat
    ensures g(x) < 10 + x
  // h names the result in just the trait
  function method h(x: nat): (res: nat)
    ensures res < 10 + x
}

class C extends T {
  // d does not name the result in either trait or class
  function method d(y: nat): nat
    ensures d(y) < 8 + y
  { 5 + y }
  // f names the result in both trait and class
  function method f(y: nat): (result: nat)
    ensures result < 8 + y
  { 5 + y }
  // g names the result in just the class
  function method g(y: nat): (result: nat)
    ensures result < 8 + y
  { 5 + y }
  // h names the result in just the trait
  function method h(y: nat): nat
    ensures h(y) < 8 + y
  { 5 + y }
}

// class D is like C, but in each case, the spec is NOT weaker than that in T
class D extends T {
  // d does not name the result in either trait or class
  function method d(y: nat): nat
    ensures d(y) < 20 + y  // error: specification is not weaker
  { 11 + y }
  // f names the result in both trait and class
  function method f(y: nat): (result: nat)
    ensures result < 20 + y  // error: specification is not weaker
  { 11 + y }
  // g names the result in just the class
  function method g(y: nat): (result: nat)
    ensures result < 20 + y  // error: specification is not weaker
  { 11 + y }
  // h names the result in just the trait
  function method h(y: nat): nat
    ensures h(y) < 20 + y  // error: specification is not weaker
  { 11 + y }
}


// class E is like D, but the function implementations still live up to T's specs
class E extends T {
  // d does not name the result in either trait or class
  function method d(y: nat): nat
    ensures d(y) < 20 + y
  { 5 + y }
  // f names the result in both trait and class
  function method f(y: nat): (result: nat)
    ensures result < 20 + y
  { 5 + y }
  // g names the result in just the class
  function method g(y: nat): (result: nat)
    ensures result < 20 + y
  { 5 + y }
  // h names the result in just the trait
  function method h(y: nat): nat
    ensures h(y) < 20 + y
  { 5 + y }
}

// class F is like C, except that the implementations don't satisfy the specs
class F extends T {
  // d does not name the result in either trait or class
  function method d(y: nat): nat  // error: postcondition violation
    ensures d(y) < 8 + y
  { 20 + y }
  // f names the result in both trait and class
  function method f(y: nat): (result: nat)  // error: postcondition violation
    ensures result < 8 + y
  { 20 + y }
  // g names the result in just the class
  function method g(y: nat): (result: nat)  // error: postcondition violation
    ensures result < 8 + y
  { 20 + y }
  // h names the result in just the trait
  function method h(y: nat): nat  // error: postcondition violation
    ensures h(y) < 8 + y
  { 20 + y }
}
