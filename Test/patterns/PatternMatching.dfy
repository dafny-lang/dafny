// RUN: %dafny /compile:3 "%s" > "%t"
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

method Main() {
  var aa := Cons(6, Nil);
  var bb := Cons(5, aa);
  var cc := Cons(4, bb);
  var dd := Cons(4, cc);
  var ee := Cons(3, dd);
  var ff := Cons(2, ee);
  var gg := Cons(1, ff);

  var r:int;
  r := NestingTest(aa);
  print "NestingTest([6]) = ", r, ", should return 6 \n";
  r := NestedVariableTest(ff);
  print "NestedVariableTest([2::3::4::5::6]) = ", r, ", should return 0 \n";
  r := ConstantTest(ee);
  print "ConstantTest([3::4::5::6]) = ", r, ", should return 2 \n";
}