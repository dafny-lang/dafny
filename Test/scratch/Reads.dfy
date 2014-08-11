class Test {
  ghost var Repr: set<object>;
  function Ok() : bool
    reads this, Repr;
  { true }

  function Bad(x: int) : bool
    reads Repr;
  { true }
}


class C { var c : C; }

function Nope(c : C) : bool
  reads c.c;
{ true }

function Okay(c : C) : bool
  reads c, if c != null then {c.c} else {};
{ true }

function Okay'(c : C) : bool
  reads {c} + if c != null then {c.c} else {};
{ true }

