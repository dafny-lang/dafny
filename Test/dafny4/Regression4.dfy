// RUN: %dafny /compile:3 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() { }

datatype Maybe<T> = Nothing | Just(T)

function fromJust<T>(x: Maybe<T>): T
    requires x.Just?
{
    match x case Just(v) => v
}

type mem = int
type AbsPTable = seq<Maybe<AbsL2PTable>>
type AbsL2PTable = seq<Maybe<AbsPTE>>
datatype AbsPTE = AbsPTE(phys: mem, write: bool, exec: bool)

ghost function WritablePagesInTable(pt:AbsPTable): set<mem>
{
    (set i, j | 0 <= i < |pt| && pt[i].Just? && 0 <= j < |fromJust(pt[i])|
        && fromJust(pt[i])[j].Just? && fromJust(fromJust(pt[i])[j]).write
        :: fromJust(fromJust(pt[i])[j]).phys)
}

method G(pt:AbsPTable, i: int, j: int)
  requires 0 <= i < |pt| && pt[i].Just? && 0 <= j < |fromJust(pt[i])|
{
  var s := pt[i];
  var aa := fromJust(s);
  var z := aa[j];
}
