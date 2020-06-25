// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


datatype Option<A> = Some(value: A) | None

datatype T<A> = T(value: Option<A>)

function f(t: T<int>) : T<int>
{
  match t.value {
    case Some(val) => T(Some(val))
    case None => (
      var none : Option<int> := None;
      T(none)
    )
  }
}

