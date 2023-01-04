// RUN: %exits-with 4 %dafny /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

codatatype Stream<T> = Cons(head: T, tail: Stream<T>)

// -----

function {:abstemious} TrivallyGood(): Stream<int>
{
  Cons(0, TrivallyGood())
}

function {:abstemious} Inc(s: Stream<int>): Stream<int>
{
  Cons(s.head + 1, Inc(s.tail))
}

function {:abstemious} Duplicate(s: Stream): Stream
{
  Cons(s.head, Cons(s.head, Duplicate(s.tail)))
}

function {:abstemious} add(a: Stream<int>, b: Stream<int>): Stream<int>
{
  Cons(a.head + b.head, add(a.tail, b.tail))
}

function voraciousAdd(a: Stream<int>, b: Stream<int>): Stream<int>
{
  Cons(a.head + b.head, voraciousAdd(a.tail, b.tail))
}

// -----

function Fib(): Stream<int>
{
  Cons(0, Cons(1,
    voraciousAdd(
      Fib(),  // error (termination): because not abstemious
      Fib().tail)))
}

function FibSortof(): Stream<int>
{
  Cons(0, Cons(1,
    voraciousAdd(
      FibSortof(),  // error (termination): because not abstemious
      FibSortof())))
}

function ThisAintGoinNowhere(): Stream<int>
{
  ThisAintGoinNowhere()  // error (termination): not sufficiently guarded
}

function BadFib(): Stream<int>
{
  Cons(1,
    add(
      BadFib(),  // error (termination): because second Bad() is in destructive context
      BadFib().tail))
}

function AnotherBadFib(): Stream<int>
{
  Cons(1,
    voraciousAdd(
      AnotherBadFib(),  // error (termination): because second Bad() is in destructive context
      AnotherBadFib().tail))
}
