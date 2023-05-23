// RUN: %exits-with 4 %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type MyInt_Bad = x | 6 <= x witness 5  // error: witness does not satisfy constraint

type MyInt = x | 6 <= x witness 6

newtype MyNewInt = x | 6 <= x witness 6

type Six = x | 6 <= x witness 6
type SixAgain = six: Six | 4 <= six  // error: the attempted witness 0 is not good enough (it's not even a Six)
type SixAgainW = six: Six | 4 <= six witness 4  // error: 4 is not a witness for the type (it's not even a Six)
type Impossible = six: Six | six < 2  // error: this would be an empty type

newtype NewSix = x | 6 <= x witness 6
newtype NewSixAgain = six: NewSix | 4 <= six as int  // error: witness 0 is not a NewSix
newtype NewSixAgainW = six: NewSix | 4 <= six as int witness 4  // error: 4 is not a NewSix
newtype NewSixAgainY = six | Yes(six) witness 4  // error: 4 is not a NewSix
newtype NewImpossible = six: NewSix | six < 6  // error: this would be an empty type

ghost predicate Yes(six: NewSix) {
  4 <= six as int
}

newtype YetAnotherNewSix = NewSix

// Now with some type parameters
datatype List<G> = Nil | Cons(G, List<G>)
function Length(xs: List): nat
{
  match xs
  case Nil => 0
  case Cons(_, tail) => Length(tail) + 1
}

type ListTwo<G> = xs: List<set<G>> | 2 <= Length(xs) witness Cons({}, Cons({}, Nil))
type TwoAgain<G> = xs: ListTwo<(set<G>,())> | 1 <= Length(xs)  // error: didn't find a good witness
type TwoAgainW<G> = xs: ListTwo<set<G>> | 1 <= Length(xs) witness Cons({}, Nil)  // error: this witness isn't even a ListTwo
type TwoImpossible<G> = xs: ListTwo<set<G>> | Length(xs) < 2  // error: this would be an empty type

// the following lines test that the appropriate lit-lifting happens
type ListFour<G> = xs: List<set<G>> | 4 <= Length(xs) witness Cons({}, Cons({}, Cons({}, Cons({}, Nil))))
type ListFour'<G> = xs: ListTwo<G> | 4 <= Length(xs) witness Cons({}, Cons({}, Cons({}, Cons({}, Nil))))

// TODO: what about the case where a constraint is excluded because of "provides"?

datatype Yt<Y> = MakeYt(x: int, y: Y)
type Even = x | x % 2 == 0
type Odd = x | x % 2 == 1 witness 17
type GW = x | x % 2 == 1 ghost witness 17
method DefiniteAssignmentViolation() returns (e: Yt<Even>, o: Yt<Odd>, g: Yt<GW>)
{
}  // error: must assign to 'g' (but 'e' and 'o' can be handled by the compiler)
method ArrayElementInitViolation() returns (e: array<Yt<Even>>, o: array<Yt<Odd>>, g: array<Yt<GW>>)
{
  e := new Yt<Even>[20];
  o := new Yt<Odd>[20];
  g := new Yt<GW>[20];  // error: must give array-element initializer
}
