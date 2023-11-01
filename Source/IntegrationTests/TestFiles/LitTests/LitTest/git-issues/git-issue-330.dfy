// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


datatype Option<A> = Some(value: A) | None

datatype T<A> = T(value: Option<A>)

ghost function f(t: T<int>) : T<int>
{
  match t.value {
    case Some(val) => T(Some(val))
    case None =>  T(None)
  }
}

ghost function fok(t: T<int>) : T<int>
{
  match t.value {
    case Some(val) => T(Some(val))
    case None => (
      var none : Option<int> := None;
      T(none)
    )
  }
}

ghost function fok1(t: T<int>) : T<int>
{
  match t.value {
    case Some(val) => T(Some(val))
    case None => T<int>.T(None)
  }
}

ghost function fok2(t: T<int>) : T<int>
{
  match t.value {
    case Some(val) => T(Some(val))
    case None => T(Option<int>.None)
  }
}

ghost function fok3(t: T<int>) : T<int>
{
  match t.value {
    case Some(val) => T(Some(val))
    case None => T<int>.T(Option<int>.None)
  }
}
