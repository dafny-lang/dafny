// RUN: %dafny /compile:3 /errorLimit:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Fruit = Apple(x: int) | Peach(y: bool)

predicate method CIsSpecial(f: Fruit) {
  match f
  case Apple(x) => x % 2 == 0
  case Peach(y) => y
}

predicate GIsSpecial(f: Fruit) {
  CIsSpecial(f)
}

type SpecialFruit = f: Fruit | GIsSpecial(f) witness Apple(0)

function method G(f: Fruit): int
  requires GIsSpecial(f)
{
  match f
  case Apple(x) => 10 / (x - 3)
  case Peach(y) => if y then 5 else G(f)
}

method Main() {
  var a := {Apple(2), Apple(3), Peach(false), Apple(4), Peach(true)};

  ghost var b := set f: SpecialFruit | f in a && G(f) < 10; // since the RHS expression occurs in a ghost context, I would not have expected an error

  ghost var yes := true;
  if yes {
    // this is a ghost context
    var c := set f: SpecialFruit | f in a && G(f) < 10; // since this is in a ghost context, I would not have expected an error
  }

  // The next line complains about cannot-be-compiled (nice), but also gives a (to the user seemingly unrelated) precondition violation.
  Print(set f: SpecialFruit | f in a && G(f) < 10);

  // The next line gives error (good), but I'm wishing for an error message that says something about compilation. How come this
  // line doesn't also give the cannot-be-compiled error that the previous line gives?
  Print(set f: SpecialFruit | G(f) < 10 && f in a && CIsSpecial(f));

  Print(set f: SpecialFruit | f in a && CIsSpecial(f) && G(f) < 10); // verifies, compiles, and runs (good!)

  Print(set f: SpecialFruit | CIsSpecial(f) && G(f) < 10 && f in a); // verifies, compiles, and runs (good!)
}

method Print(s: set<Fruit>) {
  print s, "\n";
}