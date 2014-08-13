// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Checking that the reads clause also is checked over requires

class C { var u : int; }

function nope1(c : C):()
     requires c != null && c.u > 0;
{()}

function ok1(c : C):()
     requires c != null && c.u > 0;
     reads c;
{()}

function nope2(c : C):()
     requires c != null && c.u > 0;
     reads if c != null then {} else {c};
{()}

function ok2(c : C):()
     requires c != null && c.u > 0;
     reads if c != null then {c} else {};
{()}

function nope3(xs : seq<C>):()
     requires |xs| > 0 && xs[0] != null && xs[0].u > 0;
{()}

function ok3(xs : seq<C>):()
     requires |xs| > 0 && xs[0] != null && xs[0].u > 0;
     reads xs;
{()}

function nope4(c : C, xs : set<C>):()
     requires c != null && c !in xs ==> c.u > 0;
     reads xs;
{()}

function ok4(c : C, xs : set<C>):()
     requires c != null && c in xs ==> c.u > 0;
     reads xs;
{()}

// reads over itself

class R { var r : R; }

function nope5(r : R):()
  reads if r != null then {r.r} else {};
{()}

function ok5(r : R):()
  reads if r != null then {r, r.r} else {};
{()}

