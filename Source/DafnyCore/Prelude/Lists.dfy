module Lists {
  export
    reveals List, List.Length, List.At, List.Contains, List.Append, List.Take, List.Drop, List.Split
    provides List.ContainsAt, List.AtContains, List.LengthAppend, List.AppendAt, List.AboutDrop
    provides List.AppendTake, List.TakeFromAppend, List.AppendDrop, List.DropFromAppend
    provides List.AppendTakeDrop, List.LengthTakeDrop

  datatype List<X(==)> = Nil | Cons(head: X, tail: List<X>)
  {
    function Length(): nat {
      if Nil? then 0 else 1 + tail.Length()
    }

    function Append(xs: List<X>): List<X> {
      match this
      case Nil => xs
      case Cons(x, tail) => Cons(x, tail.Append(xs))
    }

    lemma LengthAppend(xs: List<X>)
      ensures Append(xs).Length() == Length() + xs.Length()
    {
    }

    function At(i: nat): X
      requires i < Length()
    {
      if i == 0 then head else tail.At(i - 1)
    }

    predicate Contains(x: X) {
      match this
      case Nil => false
      case Cons(y, tail) => x == y || tail.Contains(x)
    }

    lemma ContainsAt(x: X) returns (i: nat)
      requires Contains(x)
      ensures i < Length() && At(i) == x
    {
      if head == x {
        return 0;
      } else {
        i := tail.ContainsAt(x);
        return i + 1;
      }
    }

    lemma AtContains(i: nat, x: X)
      requires i < Length() && At(i) == x
      ensures Contains(x)
    {
    }

    lemma ConsAt(x: X, i: nat)
      requires i < Cons(x, this).Length()
      ensures Cons(x, this).At(i) ==
              if i == 0 then x else At(i - 1)
    {
    }

    lemma AppendAt(xs: List<X>, i: nat)
      requires i < Append(xs).Length()
      ensures Append(xs).At(i) ==
              if i < Length() then At(i) else (LengthAppend(xs); xs.At(i - Length()))
    {
    }

    function Take(n: nat): List<X>
      requires n <= Length()
    {
      if n == 0 then Nil else Cons(head, tail.Take(n - 1))
    }

    function Drop(n: nat): List<X>
      requires n <= Length()
    {
      if n == 0 then this else tail.Drop(n - 1)
    }

    function Split(n: nat): (split: (List<X>, List<X>))
      requires n <= Length()
      ensures split.0.Append(split.1) == this
    {
      AppendTakeDrop(n);
      (Take(n), Drop(n))
    }

    lemma AboutDrop(n: nat)
      requires n < Length()
      ensures Drop(n).Cons?
    {
    }

    lemma AppendTake(xs: List<X>)
      ensures (LengthAppend(xs); Append(xs).Take(Length()) == this)
    {
      match this
      case Nil =>
      case Cons(x, tail) =>
        LengthAppend(xs);
    }

    lemma TakeFromAppend(xs: List<X>, n: nat)
      requires n <= Length() + xs.Length()
      ensures (LengthAppend(xs);
               Append(xs).Take(n) ==
               if n <= Length() then Take(n) else Append(xs.Take(n - Length())))
    {
      LengthAppend(xs);
    }

    lemma AppendDrop(xs: List<X>)
      ensures (LengthAppend(xs); Append(xs).Drop(Length()) == xs)
    {
      match this
      case Nil =>
      case Cons(x, tail) =>
        LengthAppend(xs);
    }

    lemma DropFromAppend(xs: List<X>, n: nat)
      requires n <= Length() + xs.Length()
      ensures (LengthAppend(xs);
               Append(xs).Drop(n) ==
               if n <= Length() then Drop(n).Append(xs) else xs.Drop(n - Length()))
    {
      LengthAppend(xs);
    }

    lemma AppendTakeDrop(i: nat)
      requires i <= Length()
      ensures Take(i).Append(Drop(i)) == this
    {
    }

    lemma LengthTakeDrop(i: nat)
      requires i <= Length()
      ensures Take(i).Length() == i && Drop(i).Length() == Length() - i
    {
    }
  }
}
