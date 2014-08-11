// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function MyReadsOk(f : A -> B, a : A) : set<object>
  reads f.reads(a);
{
  f.reads(a)
}

function MyReadsOk2(f : A -> B, a : A) : set<object>
  reads f.reads(a);
{
  (f.reads)(a)
}

function MyReadsOk3(f : A -> B, a : A) : set<object>
  reads (f.reads)(a);
{
  f.reads(a)
}

function MyReadsOk4(f : A -> B, a : A) : set<object>
  reads (f.reads)(a);
{
  (f.reads)(a)
}

function MyReadsBad(f : A -> B, a : A) : set<object>
{
  f.reads(a)
}

function MyReadsBad2(f : A -> B, a : A) : set<object>
{
  (f.reads)(a)
}

function MyReadsOk'(f : A -> B, a : A, o : object) : bool
  reads f.reads(a);
{
  o in f.reads(a)
}

function MyReadsBad'(f : A -> B, a : A, o : object) : bool
{
  o in f.reads(a)
}

function MyRequiresOk(f : A -> B, a : A) : bool
  reads f.reads(a);
{
  f.requires(a)
}

function MyRequiresBad(f : A -> B, a : A) : bool
{
  f.requires(a)
}

