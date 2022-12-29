// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type A = s: object | true witness this
const x: object := this
type St_ = map<nat,Ob>
type Ob {
    predicate i(s:St_)
}
type St = s:St_ | (forall o | o in s.Values :: o.i(this))
