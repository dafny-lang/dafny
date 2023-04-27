// RUN: %dafny /compile:3 /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Apply<A,B>(f: A ~> B, x: A): B
  reads f.reads(x);
  requires f.requires(x);
{
  f(x)
}

function Apply'<A,B>(f: A ~> B) : A ~> B
{
  x reads f.reads(x)
    requires f.requires(x)
    => f(x)
}


function Compose<A,B,C>(f: B ~> C, g:A ~> B): A ~> C
{
  x reads g.reads(x)
    reads if g.requires(x) then f.reads(g(x)) else {}
    requires g.requires(x)
    requires f.requires(g(x))
    => f(g(x))
}

function W<A>(f : (A,A) ~> A): A ~> A
{
  x requires f.requires(x,x)
    reads f.reads(x,x)
    => f(x,x)
}

function Curry<A,B,C>(f : (A,B) ~> C) : A ~> B ~> C
{
  x => y requires f.requires(x,y)
         reads f.reads(x,y)
         => f(x,y)
}

function Uncurry<A,B,C>(f : A ~> B ~> C) : (A,B) ~> C
{
  (x,y) requires f.requires(x)
        requires f(x).requires(y)
        reads f.reads(x)
        reads if f.requires(x) then f(x).reads(y) else {}
        => f(x)(y)
}

function S<A,B,C>(f : (A,B) ~> C, g : A ~> B): A ~> C
{
  x requires g.requires(x)
    requires f.requires(x,g(x))
    reads g.reads(x)
    reads if g.requires(x) then f.reads(x,g(x)) else {}
    => f(x,g(x))
}
