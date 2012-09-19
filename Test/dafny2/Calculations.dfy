/* Lists */
// Here are some standard definitions of List and functions on Lists

datatype List<T> = Nil | Cons(T, List);

function length(l: List): nat
{
  match l
  case Nil => 0
  case Cons(x, xs) => 1 + length(xs)
}

function concat(l: List, ys: List): List
{
  match l
  case Nil => ys
  case Cons(x, xs) => Cons(x, concat(xs, ys))
}

function reverse(l: List): List
{
  match l
  case Nil => Nil
  case Cons(x, xs) => concat(reverse(xs), Cons(x, Nil))
}

function revacc(l: List, acc: List): List
{
  match l
  case Nil => acc
  case Cons(x, xs) => revacc(xs, Cons(x, acc))
}

function qreverse(l: List): List
{
  revacc(l, Nil)
}

// Here are two lemmas about the List functions.

ghost method Lemma_ConcatNil()
  ensures forall xs :: concat(xs, Nil) == xs;
{
}

ghost method Lemma_RevCatCommute()
  ensures forall xs, ys, zs :: revacc(xs, concat(ys, zs)) == concat(revacc(xs, ys), zs);
{
}

// Here is a theorem that says "qreverse" and "reverse" calculate the same result.  The proof
// is given in a calculational style.  The proof is not minimal--some lines can be omitted
// and Dafny will still fill in the details.

ghost method Theorem_QReverseIsCorrect_Calc(l: List)
  ensures qreverse(l) == reverse(l);
{
  calc {
    qreverse(l);
    // def. qreverse
    revacc(l, Nil);
    { Lemma_Revacc_calc(l, Nil); }
    concat(reverse(l), Nil);
    { Lemma_ConcatNil(); }
    reverse(l);
  }
}

ghost method Lemma_Revacc_calc(xs: List, ys: List)
  ensures revacc(xs, ys) == concat(reverse(xs), ys);
{
  match (xs) {
    case Nil =>
    case Cons(x, xrest) =>
      calc {
        concat(reverse(xs), ys);
        // def. reverse
        concat(concat(reverse(xrest), Cons(x, Nil)), ys);
        // induction hypothesis: Lemma_Revacc_calc(xrest, Cons(x, Nil))
        concat(revacc(xrest, Cons(x, Nil)), ys);
        { Lemma_RevCatCommute(); } // forall xs,ys,zs :: revacc(xs, concat(ys, zs)) == concat(revacc(xs, ys), zs)
        revacc(xrest, concat(Cons(x, Nil), ys));
        { 
          assert forall g, gs :: concat(Cons(g, Nil), gs) == Cons(g, gs); 
          assert concat(Cons(x, Nil), ys) == Cons(x, ys);
        }
        revacc(xrest, Cons(x, ys));
        // def. revacc
        revacc(xs, ys);
      }
  }
}

// Here is a version of the same proof, as it was constructed before Dafny's "calc" construct.

ghost method Theorem_QReverseIsCorrect(l: List)
  ensures qreverse(l) == reverse(l);
{
  assert qreverse(l)
      == // def. qreverse
         revacc(l, Nil);
  Lemma_Revacc(l, Nil);
  assert revacc(l, Nil)
      == concat(reverse(l), Nil);
  Lemma_ConcatNil();
}

ghost method Lemma_Revacc(xs: List, ys: List)
  ensures revacc(xs, ys) == concat(reverse(xs), ys);
{
  match (xs) {
    case Nil =>
    case Cons(x, xrest) =>
      assert revacc(xs, ys)
          == // def. revacc
              revacc(xrest, Cons(x, ys));

      assert concat(reverse(xs), ys)
          == // def. reverse
              concat(concat(reverse(xrest), Cons(x, Nil)), ys)
          == // induction hypothesis:  Lemma3a(xrest, Cons(x, Nil))
              concat(revacc(xrest, Cons(x, Nil)), ys);
          Lemma_RevCatCommute();  // forall xs,ys,zs :: revacc(xs, concat(ys, zs)) == concat(revacc(xs, ys), zs)
      assert concat(revacc(xrest, Cons(x, Nil)), ys)
          == revacc(xrest, concat(Cons(x, Nil), ys));

      assert forall g, gs :: concat(Cons(g, Nil), gs) == Cons(g, gs);

      assert revacc(xrest, concat(Cons(x, Nil), ys))
          == // the assert lemma just above
              revacc(xrest, Cons(x, ys));
  }
}

/* Fibonacci */
// To further demonstrate what the "calc" construct can do, here are some proofs about the Fibonacci function.

function Fib(n: nat): nat
{
  if n < 2 then n else Fib(n - 2) + Fib(n - 1)
}

ghost method Lemma_Fib()
  ensures Fib(5) < 6;
{
  calc {
    Fib(5);
    Fib(4) + Fib(3);
    calc {
      Fib(2);
      Fib(0) + Fib(1);
      0 + 1;
      1;
    }
    < 6;
  }
}

/* List length */
// Here are some proofs that show the use of nested calculations.

ghost method Lemma_Concat_Length(xs: List, ys: List)
  ensures length(concat(xs, ys)) == length(xs) + length(ys);
{}

ghost method Lemma_Reverse_Length(xs: List)
  ensures length(xs) == length(reverse(xs));
{
  match (xs) {
    case Nil =>
    case Cons(x, xrest) =>
      calc {
        length(reverse(xs));
        // def. reverse
        length(concat(reverse(xrest), Cons(x, Nil)));
        { Lemma_Concat_Length(reverse(xrest), Cons(x, Nil)); }
        length(reverse(xrest)) + length(Cons(x, Nil));
        // induction hypothesis
        length(xrest) + length(Cons(x, Nil));
        calc {
          length(Cons(x, Nil));
          // def. length
          1 + length(Nil);
          // def. length
          1 + 0;
          1;
        }
        length(xrest) + 1;
        // def. length
        length(xs);
      }
  }
}

ghost method Window(xs: List, ys: List)
  ensures length(xs) == length(ys) ==> length(reverse(xs)) == length(reverse(ys));
{
  calc {
    length(xs) == length(ys) ==> length(reverse(xs)) == length(reverse(ys));
    { if (length(xs) == length(ys)) {
      calc {
        length(reverse(xs));
        { Lemma_Reverse_Length(xs); }
        length(xs);
        length(ys);
        { Lemma_Reverse_Length(ys); }
        length(reverse(ys));
    } } }
    length(xs) == length(ys) ==> length(reverse(xs)) == length(reverse(xs));
    true;
  }
}