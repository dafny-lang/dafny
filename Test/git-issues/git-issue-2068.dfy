// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type St = s:St_ | (forall o | o in s :: o.i(this))
type St_ = map<nat,Ob>
type Ob {
    predicate i(s:St_)
}