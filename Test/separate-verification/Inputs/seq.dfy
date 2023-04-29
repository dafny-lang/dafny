
module Seq {

  import opened Wrappers

  /* explains associative property of sequences in addition */
  lemma LemmaConcatIsAssociative<T>(a: seq<T>, b: seq<T>, c: seq<T>)
    ensures a + (b + c) == (a + b) + c;
  {
  }

  function {:opaque} IndexOfOption<T(==)>(s: seq<T>, v: T): (o: Option<nat>)
    ensures if o.Some? then o.value < |s| && s[o.value] == v &&
                            forall j {:trigger s[j]} :: 0 <= j < o.value ==> s[j] != v
            else v !in s
  {
    if |s| == 0 then None()
    else
      if s[0] == v then Some(0)
      else
        var o' := IndexOfOption(s[1..], v);
        if o'.Some? then Some(o'.value + 1) else None()
  }
}