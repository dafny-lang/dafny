function Fib(n: int): int
  requires 0 <= n;
  ensures 0 <= Fib(n);
{
  if n < 2 then n else
  Fib(n-2) + Fib(n-1)
}

datatype List = Nil | Cons(int, List);

function Sum(a: List): int
  ensures 0 <= Sum(a);
{
  match a
  case Nil => 0
  case Cons(x, tail) => if x < 0 then 0 else Fib(x)
}

function FibWithoutPost(n: int): int
  requires 0 <= n;
{
  if n < 2 then n else
  FibWithoutPost(n-2) + FibWithoutPost(n-1)
}

function SumBad(a: List): int
  ensures 0 <= Sum(a);  // this is still okay, because this is calling the good Sum
  ensures 0 <= SumBad(a);  // error: cannot prove postcondition
{
  match a
  case Nil => 0
  case Cons(x, tail) => if x < 0 then 0 else FibWithoutPost(x)
}

function FibWithExtraPost(n: int): int
  ensures 2 <= n ==> 0 <= FibWithExtraPost(n-1); // This is fine, because the definition of the function is discovered via canCall
  ensures 1 <= n ==> 0 <= FibWithExtraPost(n-1); // Error: In the current implementation of Dafny, one needs to actually call the
                                                 // function in order to benefit from canCall.  This may be improved in the future.
  ensures 0 <= FibWithExtraPost(n);
{
  if n < 0 then 0 else
  if n < 2 then n else
  FibWithExtraPost(n-2) + FibWithExtraPost(n-1)
}

function DivergentPost(n: int): int
  requires 0 <= n;
  ensures 1 <= n ==> DivergentPost(n-1) == DivergentPost(n-1);
  ensures DivergentPost(2*n - n) == DivergentPost(2*(n+5) - 10 - n);  // these are legal ways to denote the result value of the function
  ensures DivergentPost(n+1) == DivergentPost(n+1);  // error: call may not terminate
{
  if n < 2 then n else
  DivergentPost(n-2) + DivergentPost(n-1)
}
