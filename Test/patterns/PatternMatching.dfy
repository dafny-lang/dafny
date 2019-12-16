// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
*  This file contains a collection of tests for features modified or introduced in PR 458
*/


datatype Alt = A(int) | B(int)
datatype MyOption = Some(v: Alt) | None
datatype MyPair = Pair(x:Alt, y:Alt)
datatype List<T> = Nil | Cons(head: T, tail: List)



// Nested Patterns
method NestingTest (xs:List<int>) returns (r:int)
{
    match xs
     case Cons(y, Cons(z, zs)) => return z;
     case Cons(y, Nil) => return y;
     case Nil => return 0;
}


// Ordered match with variables
method NestedVariableTest(x:List<int>) returns (r:int)
{
    match x {
        case Cons(a, Cons(b, tl1)) => r := 0;
        case Cons(c, tl2) => r:=1;
        case d => r := 2;
    }
}

// Nested, Ordered patterns
method OrderedTest(x: MyOption ) returns (r: int)
{
    match x {
        case Some(A(i)) => r:=0;
        case Some(_) => r := 1;
	case None => r := 2;
   }
}

// Empty matching context
method VariableTest(x:List<int>) returns (r:int)
{
    match x {
        case a => r := 1;
    }
}


// Test interleaving of constant and constructor testing
method ConstantTest(x:List<int>) returns (r:int)
{
    match x {
        case Cons(1, tl1) => r := 0;
        case Cons(c, Cons(2, tl2)) => r:=1;
        case d => r := 2;
    }
}

// Nested, ordered expression match
lemma sorted_inv(z: int, l: List<int>)
{
  match l {
    case Nil =>
    case Cons(a, Cons(b, Cons(c, Nil))) =>
    case Cons(a, b) =>
  }
}