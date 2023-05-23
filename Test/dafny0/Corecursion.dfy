// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// --------------------------------------------------

module CoRecursion {
  codatatype Stream<T> = More(head: T, rest: Stream)

  ghost function AscendingChain(n: int): Stream<int>
  {
    More(n, AscendingChain(n+1))
  }

  ghost function AscendingChainAndRead(n: nat): Stream<int>
    reads null;  // with a reads clause, this function is not a co-recursive function
  {
    More(n, AscendingChainAndRead(n+1))  // error: cannot prove termination
  }

  ghost function AscendingChainAndPostcondition(n: nat): Stream<int>
    ensures false;  // with an ensures clause, this function is not a co-recursive function
  {
    More(n, AscendingChainAndPostcondition(n+1))  // error: cannot prove termination
  }

  datatype List<T> = Nil | Cons(T, List)

  ghost function Prefix(n: nat, s: Stream): List
  {
    if n == 0 then Nil else
    Cons(s.head, Prefix(n-1, s.rest))
  }
}

// --------------------------------------------------

module CoRecursionNotUsed {
  codatatype Stream<T> = More(T, Stream)

  ghost function F(s: Stream, n: nat): Stream
    decreases n, true;
  {
    G(s, n)
  }
  ghost function G(s: Stream, n: nat): Stream
    decreases n, false;
  {
    if n == 0 then s else Tail(F(s, n-1))
  }

  ghost function Tail(s: Stream): Stream
  {
    match s case More(hd, tl) => tl
  }

  ghost function Diverge(n: nat): nat
  {
    Diverge(n)  // error: cannot prove termination
  }
}

// --------------------------------------------------

module EqualityIsSuperDestructive {
  codatatype Stream<T> = Cons(head: T, tail: Stream)

  ghost function F(s: Stream<int>): Stream<int>
  {
    // Co-recursive calls are not allowed in arguments of equality, so the following call to
    // F(s) is a recursive call.
    if Cons(1, F(s)) == Cons(1, Cons(1, s))  // error: cannot prove termination
    then Cons(2, s) else Cons(1, s)
  }

  lemma Lemma(s: Stream<int>)
  {
    // The following three assertions follow from the definition of F, so F had better
    // generate some error (which it does -- the recursive call to F in F does not terminate).
    assert F(s) == Cons(1, s);
    assert F(s) == Cons(2, s);
    assert false;
  }
}

// --------------------------------------------------

module MixRecursiveAndCorecursive {
  codatatype Stream<T> = Cons(head: T, tail: Stream)

  ghost function F(n: nat): Stream<int>
  {
    if n == 0 then
      Cons(0, F(5))  // error: cannot prove termination -- by itself, this would look like a properly guarded co-recursive call...
    else
      F(n - 1).tail  // but the fact that this recursive call is not tail recursive means that call in the 'then' branch is not
                     // allowed to be a co-recursive
  }

  // same thing but with some mutual recursion going on
  ghost function G(n: nat): Stream<int>
  {
    if n == 0 then
      Cons(0, H(5))  // error: cannot prove termination
    else
      H(n)
  }
  ghost function H(n: nat): Stream<int>
    requires n != 0;
    decreases n, 0;
  {
    G(n-1).tail
  }

  // but if all the recursive calls are tail recursive, then all is cool
  ghost function X(n: nat): Stream<int>
  {
    if n == 0 then
      Cons(0, Y(5))  // error: cannot prove termination
    else
      Y(n)
  }
  ghost function Y(n: nat): Stream<int>
    requires n != 0;
    decreases n, 0;
  {
    X(n-1)
  }
}

// --------------------------------------------------

module FunctionSCCsWithMethods {
  codatatype Stream<T> = Cons(head: T, tail: Stream)

  lemma M(n: nat)
    decreases n, 0;
  {
    if n != 0 {
      var p := Cons(10, F(n-1));
    }
  }

  ghost function F(n: nat): Stream<int>
    decreases n;
  {
    M(n);
    // the following call to F is not considered co-recursive, because the SCC contains a method
    Cons(5, F(n))  // error: cannot prove termination
  }

  ghost function G(): Stream<int>
  {
    Lemma();
    H()
  }

  ghost function H(): Stream<int>
    decreases 0;
  {
    // the following call to G is not considered co-recursive, because the SCC contains a method
    Cons(5, G())  // error: cannot prove termination
  }

  lemma Lemma()
    decreases 1;
  {
    var h := H();
  }
}

// --------------------------------------------------

module AutomaticPrefixingOfCoClusterDecreasesClauses {
  codatatype Stream<T> = Cons(head: T, tail: Stream)

  // The following three functions will verify automatically
  ghost function H(): Stream<int>  // automatic:  decreases 1;
  {
    F(true)
  }
  ghost function F(b: bool): Stream<int>  // automatic:  decreases 0, b;
  {
    if b then Cons(5, G()) else Cons(7, H())
  }
  ghost function G(): Stream<int>  // automatic:  decreases 1;
  {
    F(false)
  }

  // In the following, A gets a default decreases clause of 1, because
  // the only recursive call to A is a self-call.  B, on the other
  // hand, has a mutually recursive call from A, and therefore it gets
  // a decreases clause of 0.
  ghost function A(n: nat): Stream<int>  // automatic:  decreases 1, n;
  {
    if n < 100 then
      B(n)  // the automatic decreases clauses take care of the termination of this call
    else
      A(n - 1)  // termination proved on account of decreasing 1,n
  }
  ghost function B(n: nat): Stream<int>  // automatic:  decreases 0, n;
  {
    if n < 100 then
      Cons(n, A(n + 102))  // co-recursive call, so no termination check
    else
      B(n - 1)  // termination proved on account of decreasing 0,n
  }
}
