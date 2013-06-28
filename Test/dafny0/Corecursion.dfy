
// --------------------------------------------------

module CoRecursion {
  codatatype Stream<T> = More(head: T, rest: Stream);

  function AscendingChain(n: int): Stream<int>
  {
    More(n, AscendingChain(n+1))
  }

  function AscendingChainAndRead(n: nat): Stream<int>
    reads this;  // with a reads clause, this function is not a co-recusvie function
  {
    More(n, AscendingChainAndRead(n+1))  // error: cannot prove termination
  }

  datatype List<T> = Nil | Cons(T, List);

  function Prefix(n: nat, s: Stream): List
  {
    if n == 0 then Nil else
    Cons(s.head, Prefix(n-1, s.rest))
  }
}

// --------------------------------------------------

module CoRecursionNotUsed {
  codatatype Stream<T> = More(T, Stream);

  function F(s: Stream, n: nat): Stream
    decreases n, true;
  {
    G(s, n)
  }
  function G(s: Stream, n: nat): Stream
    decreases n, false;
  {
    if n == 0 then s else Tail(F(s, n-1))
  }

  function Tail(s: Stream): Stream
  {
    match s case More(hd, tl) => tl
  }

  function Diverge(n: nat): nat
  {
    Diverge(n)  // error: cannot prove termination
  }
}

// --------------------------------------------------

module EqualityIsSuperDestructive {
  codatatype Stream<T> = Cons(head: T, tail: Stream)

  function F(s: Stream<int>): Stream<int>
  {
    // Co-recursive calls are not allowed in arguments of equality, so the following call to
    // F(s) is a recursive call.
    if Cons(1, F(s)) == Cons(1, Cons(1, s))  // error: cannot prove termination
    then Cons(2, s) else Cons(1, s)
  }

  ghost method lemma(s: Stream<int>)
  {
    // The following three assertions follow from the definition of F, so F had better
    // generate some error (which it does -- the recursive call to F in F does not terminate).
    assert F(s) == Cons(1, s);
    assert F(s) == Cons(2, s);
    assert false;
  }
}
