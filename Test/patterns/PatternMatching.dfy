// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
*  This file contains a collection of tests for features modified or introduced in PR 458
*/


datatype Alt = A(int) | B(int)
datatype MyOption = Some(v: Alt) | None
datatype MyPair = Pair(x: Alt, y: Alt)
datatype List<T> = Nil | Cons(head: T, tail: List)

// Nested Patterns
method NestingTest(xs: List<int>) returns (r: int)
{
  match xs {
    case Cons(y, Cons(z, zs)) => return z;
    case Cons(y, Nil) => return y;
    case Nil => return 0;
  }
}


// Ordered match with variables
method NestedVariableTest(x: List<int>) returns (r: int)
{
  match x {
    case Cons(a, Cons(b, tl1)) => r := 0;
    case Cons(c, tl2) => r := 1;
    case d => r := 2;
  }
}

// Nested, Ordered patterns
method OrderedTest(x: MyOption ) returns (r: int)
  ensures x == None ==> r == 2
  ensures x != None ==> r < 2
{
  match x {
    case Some(A(i)) => r := 0;
    case Some(_) => r := 1;
    case None => r := 2;
  }
}

// Empty matching context
method VariableTest(x: List<int>) returns (r: int)
{
  match x {
    case a => assert a == x; r := 1;
  }
}


// Test interleaving of constant and constructor testing
method ConstantTest(x: List<int>) returns (r: int)
{
  match x {
    case Cons(1, tl1) => r := 0;
    case Cons(c, Cons(2, tl2)) => r := 1;
    case d => r := 2;
  }
}

// Nested, ordered expression match
lemma SortedInv(z: int, l: List<int>)
{
  match l {
    case Nil =>
    case Cons(a, Cons(b, Cons(c, Nil))) =>
    case Cons(a, b) =>
  }
}


// Boolean literals test, without default case
method BoolTest(x: bool) returns (r: int)
{
  match x {
    case true => r := 0;
    case false => r := 1;
  }
}

// Literal tests, with a default case
method IntTest(x: int) returns (r: int)
{
  match x {
    case 1 => r := 0;
    case 2 => r := 1;
    case n => r := n;
  }
}

method StringTest(x: string) returns (r: int)
 ensures r == 2 || x == "zero" || x == "one"
{
  match x {
    case "zero" => r := 0;
    case "one" => r := 1;
    case "one" => r := 3;  // unreachable
    case c => r := 2;
  }
}

method CharTest(x: char) returns (r: int)
{
  match x {
    case 'a' => r := 0;
    case 'b' => r := 1;
    case n => r := 2;
  }
}

method RealTest(x: real) returns (r: int)
{
  match x {
    case 1.0 => r := 0;
    case 1609.344 => r := 1;
    case c => r := 2;
  }
}

newtype N = x | x == 0 || x == 3 || x == 7

method NewTypeTest() returns (r: int)
  ensures r == 1
{
  var u: N := 3;
  match u {
    case 0 => r := 0;
    case 3 => r := 1;
    case 7 => r := 2;
  }
  return;
}

datatype PairOfNumbers = P(0:int, 1:int)
method M(p: PairOfNumbers) returns (r:int)
  ensures p.0 == 11 && p.1 == 10 ==> r == 0
  ensures p.0 == 11 && p.1 != 10 ==> r == 1
  ensures p.0 == 11 || p.1 == 11 || r == 3
{
  match p
  case P(11, 10) => assert p.0 != 10; r := 0;
  case P(11, a) => r := 1;
  case P(10, 11) => assert p.1 == 11; r := 2;
  case _ => r := 3;
}

datatype Tree = Leaf | Branch(left:Tree, b:bool, right: Tree)

method MultipleNestedMatch(x: Alt, y: Tree, z: List<nat>) returns (r: nat)
{
  match x {
    case A(i) =>
      match y {
        case Branch(_, _, Branch(_, b, _)) =>
	  match (b, z) {
	    case (true, Cons(n, _)) => r := n;
	    case (_, Nil) => r := 1;
	    case (false, Cons(n, _)) => r := n+1;
	  }
	case Branch(Branch(_, b, _), _, _) =>
	  match (b, z) {
	    case (true, Cons(n, _)) => r := n;
	    case (false, Cons(n, _)) => r := n+1;
	    case (_, Nil) => r := 2;
	  }
	case _ => r := 0;
      }
    case B(i) => r := 3;
  }
}


// matching on Seq is not supported by the parser
/*
method SequenceTest(x: seq<int>) returns (r: int)
{
  match x {
    case [3, 1, 4, 1, 5, 9, 3] => r := 7;
    case [] => r := 0;
    case s  => r := -1;
  }
}
*/

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
  print "NestingTest([6]) = ", r, ", should return 6\n";
  r := NestedVariableTest(ff);
  print "NestedVariableTest([2::3::4::5::6]) = ", r, ", should return 0\n";
  r := ConstantTest(ee);
  print "ConstantTest([3::4::5::6]) = ", r, ", should return 2\n";

  r := M(P(11,10));
  print "M(P(11,10)) = ", r, ", should return 0\n";
  r := M(P(-1,10));
  print "M(P(-1,10)) = ", r, ", should return 3\n";

  var t1 := Branch(Leaf, true, Leaf);
  var t2 := Branch(t1, false, Leaf);
  var t3 := Branch(t2, true, t2);
  var t4 := Branch(Leaf, false, t3);

  var r0 := MultipleNestedMatch(A(0), t1, gg);
  var r1 := MultipleNestedMatch(A(0), t3, Nil);
  var r2 := MultipleNestedMatch(A(0), t2, Nil);
  var r3 := MultipleNestedMatch(B(0), t3, ff);
  var r4 := MultipleNestedMatch(A(0), t3, ee);
  var r5 := MultipleNestedMatch(A(0), t4, bb);
  print "Testing MultipleNestedMatch: ", r0, r1, r2, r3, r4, r5, ", should return 012345\n";

}
