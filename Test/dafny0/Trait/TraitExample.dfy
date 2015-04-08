// RUN: %dafny /compile:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Automobile {
  ghost var Repr: set<object>
  predicate Valid()
    reads this //, Repr
    ensures Valid() ==> this in Repr
  function method Brand(): string
  var position: int
  method Drive()
    requires Valid()
    modifies this // Repr
    ensures old(position) <= position
}

class Volvo extends Automobile {
  predicate Valid()
    reads this //, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr
  }
  constructor()
    modifies this
    ensures Valid()
  {
    Repr := {this};
  }
  function method Brand(): string {
    "Volvo"
  }
  method Drive()
//    requires Valid()
    modifies this // Repr
    ensures old(position) <= position
  {
    position := position + 10;
  }
}

class Fiat extends Automobile {
  predicate Valid()
    reads this // , Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr
  }
  constructor()
    modifies this
    ensures Valid()
  {
    Repr := {this};
  }
  function method Brand(): string {
    "Fiat"
  }
  method Drive()
//    requires Valid()
    modifies this // Repr
    ensures old(position) <= position
  {
    position := position + 3;
  }
}

method Main() {
  var auto: Automobile;
  auto := new Volvo();
  WorkIt(auto);
  auto := new Fiat();
  WorkIt(auto);
}

method WorkIt(auto: Automobile)
  requires auto != null && auto.Valid()
  modifies auto // auto.Repr
{
  auto.Drive();
  print auto.Brand(), ": ", auto.position, "\n";
  auto.position := 0;
}
