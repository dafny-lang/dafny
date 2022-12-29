// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


datatype Option<A> = Some(value: A) | None

datatype T<A> = T(value: Option<A>)

function f(t: T<int>) : T<int>
{
  match t.value {
    case Some(val) => T(Some(val))
    case None =>  T(None)
  }
}

function fok(t: T<int>) : T<int>
{
  match t.value {
    case Some(val) => T(Some(val))
    case None => (
      var none : Option<int> := None;
      T(none)
    )
  }
}

function fok1(t: T<int>) : T<int>
{
  match t.value {
    case Some(val) => T(Some(val))
    case None => T<int>.T(None)
  }
}

function fok2(t: T<int>) : T<int>
{
  match t.value {
    case Some(val) => T(Some(val))
    case None => T(Option<int>.None)
  }
}

function fok3(t: T<int>) : T<int>
{
  match t.value {
    case Some(val) => T(Some(val))
    case None => T<int>.T(Option<int>.None)
  }
}
