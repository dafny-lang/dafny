// RUN:   %baredafny run --use-basename-for-filename --cores:2 --verification-time-limit:300 "%s" > "%t"
// RUN: ! %baredafny run --use-basename-for-filename --cores:2 --verification-time-limit:300 --track-print-effects "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Main\n"; // error: cannot print from this method
  P(); // error: cannot call printing method
  var iter0 := new NoPrintIter(3);
  var iter1 := new PrintIter(3);
  var _ := iter0.MoveNext();
  var _ := iter1.MoveNext(); // error: cannot call printing method
  var cl0 := new Cl.NoPrint();
  var cl1 := new Cl.Print(); // error: cannot call printing constructor
}

method {:print} P() {
  print "method P here\n";
  M();
  var iter0 := new NoPrintIter(3);
  var iter1 := new PrintIter(3);
  print "calling MoveNexts\n";
  MoveNexts(iter0, iter1);
  var cl := new Cl.NoPrint();
  cl := new Cl.Print();

  TestOverrides();
}

method MoveNexts(iter0: NoPrintIter, iter1: PrintIter)
  requires iter0.Valid() && iter1.Valid()
  requires iter0._modifies == iter0._new == iter0._reads == {}
  requires iter1._modifies == iter1._new == iter1._reads == {}
  modifies iter0, iter1
{
  var more0 := iter0.MoveNext();
  var more1 := iter1.MoveNext(); // error: cannot print from this method
}

method M() {
  var x := F(3);
  print "bye, from M\n"; // error: cannot print from this method
}

function F(x: int): int {
  10
} by method {
  print "function-by-method F\n"; // error: cannot print from this method
  return 10;
}

iterator NoPrintIter(a: int) yields (x: int)
{
  print "Start of Iter 0\n"; // error: cannot print from this method
  yield 3 + a;
  print "End of Iter 0\n"; // error: cannot print from this method
}

iterator {:print} PrintIter(a: int) yields (x: int)
{
  print "Start of Iter 1\n";
  yield 3 + a;
  print "End of Iter 1\n";
}

class Cl {
  constructor NoPrint() {
    print "Cl.NoPrint ctor\n"; // error: cannot print from this method
  }
  constructor {:print} Print() {
    print "Cl.Print ctor\n";
  }
}

trait Trait {
  method {:print} MayPrint()
  method {:print} AlwaysPrints()
}

class Overrides extends Trait {
  method MayPrint() { // allowed to drop {:print} attribute
    print "Override X"; // error: cannot print without a {:print} attribute
  }
  method {:print} AlwaysPrints() {
    print " Y\n";
  }
}

method {:print} TestOverrides() {
  var c: Overrides := new Overrides;
  var t: Trait := c;

  t.MayPrint();
  t.AlwaysPrints();

  c.MayPrint();
  c.AlwaysPrints();

  TestOverridesNoPrint(c, t);
}

method TestOverridesNoPrint(c: Overrides, t: Trait) {
  t.MayPrint(); // error: cannot call printing method
  t.AlwaysPrints(); // error: cannot call printing method

  c.MayPrint();
  c.AlwaysPrints(); // error: cannot call printing method
}
