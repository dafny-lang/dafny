// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


// -----

function Func<T(00)>(): int {
  5
}

type PossiblyEmpty = x: int | true witness *

method Test()
{
  ghost var w;
  w := Func<PossiblyEmpty>();  // error: PossiblyEmpty is not known to be nonempty
}

// -----

ghost function GetInhabitant<T(0)>(): T {
  var x: T :| true; x
}

type EmptyInt = x: int | false witness *

lemma False()
  ensures false
{
  ghost var w := GetInhabitant<EmptyInt>();  // error: type parameter must support auto-init
}
