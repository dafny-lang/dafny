// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype list<A> = Nil | Cons(head: A, tail: list<A>)
datatype d = A | B(ds: list<d>)
datatype d2 = A2 | B2(ds: seq<d2>)
datatype d3 = A3 | B3(ds: set<d3>)

ghost function d_size(x: d): int
{
  match x
  case A => 1
  case B(ds) => 1+ds_size(ds)
}

ghost function ds_size(xs: list<d>): int
{
  match xs
  case Nil => 1
  case Cons(head, tail) => d_size(head)+ds_size(tail)
}

ghost function d2_size(x: d2): int
{
  match x
  case A2 => 1
  case B2(ds) => 1+ds2_size(ds)
}

ghost function ds2_size(xs: seq<d2>): int
{
  if (|xs|==0) then 1 else 1+d2_size(xs[0])+ds2_size(xs[1..])
}

ghost function seq_dec_drop(xs: seq<int>): int
{
  if (|xs|==0) then 0 else
  1+seq_dec_drop(xs[1..])
}

ghost function seq_dec_take(xs: seq<int>): int
{
  if (|xs|==0) then 0 else
  1+seq_dec_take(xs[..|xs|-1])
}

ghost function seq_dec(xs: seq<int>): int
{
  if (|xs|==0) then 0 else
  var i :| 0 < i <= |xs|;
  i+seq_dec(xs[i..])
}

ghost function seq_dec'(xs: seq<int>): int
{
  if (|xs|==0) then 0 else
  var i :| 0 <= i < |xs|;
  i+seq_dec'(xs[..i])
}

ghost function seq_dec''(xs: seq<int>): int
{
  if (|xs|==0) then 0 else
  var i :| 0 <= i < |xs|;
  assert xs[0..i] == xs[..i];
  i+seq_dec''(xs[0..i])
}

ghost function seq_dec'''(xs: seq<int>): int
  decreases |xs|;
{
  if (|xs|==0) then 0 else
  var i :| 0 <= i < |xs|;
  i+seq_dec'''(xs[..i]+xs[i+1..])
}

ghost function seq_dec''''(xs: seq<int>): int
{
  if (|xs|==0) then 0 else
  var i :| 0 <= i < |xs|;
  i+seq_dec''''(xs[..i]+xs[i+1..])
}
