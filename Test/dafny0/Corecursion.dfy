
// --------------------------------------------------

module CoRecursion {
  codatatype Stream<T> = More(head: T, rest: Stream);

  function AscendingChain(n: int): Stream<int>
  {
    More(n, AscendingChain(n+1))
  }

  function AscendingChainAndRead(n: int): Stream<int>
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
