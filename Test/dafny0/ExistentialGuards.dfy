// RUN: %dafny /dprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(n: int)

predicate R(r: real)

method M0()
{
  if x :| P(x) {
  }
}

method M1()
{
  if x: int :| P(x) {
  }
}

method M2()
{
  if x, y :| P(x) && R(y) {
  }
}

method M3()
{
  if x: int, y :| P(x) && R(y) {
  }
}

method M4()
{
  if x, y: real :| P(x) && R(y) {
  }
}

method M5()
{
  if x: int, y: real :| P(x) && R(y) {
  }
}

method M6()
{
  if x {:myattribute x, "hello"} :| P(x) {
  }
  if x, y {:myattribute y, "sveika"} :| P(x) && R(y) {
  }
  if x: int {:myattribute x, "chello"} :| P(x) {
  }
  if x {:myattribute x, "hola"} {:yourattribute x + x, "hej"} :| P(x) {
  }
}

method M7()
{
  if x :| P(x) {
  } else if * {
  } else if y :| R(y) {
  } else if y :| P(y) {
  }
}

method P0(m: int, n: int)
  requires m < n
{
  if {
    case x :| P(x) =>
    case x: int :| P(x) =>
    case x, y :| P(x) && R(y) =>
    case x: int, y :| P(x) && R(y) =>
    case m < n =>  // just to be different
    case x, y: real :| P(x) && R(y) =>
    case x: int, y: real :| P(x) && R(y) =>
  }
}

method P1(m: int, n: int)
  requires m < n
{
  if {
    case x {:myattribute x, "hello"} :| P(x) =>
    case x, y {:myattribute y, "sveika"} :| P(x) && R(y) =>
    case x: int {:myattribute x, "chello"} :| P(x) =>
    case x {:myattribute x, "hola"} {:yourattribute x + x, "hej"} :| P(x) =>
    case m < n =>
  }
}
