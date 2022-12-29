// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Automobile {
  ghost var Repr: set<object>
  predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  function method Brand(): string
  var position: int
  method Drive()
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures old(position) <= position
}

class Fiat extends Automobile {
  predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr && position <= 100
  }
  constructor (pos: int)
    requires pos <= 100
    ensures Valid() && fresh(Repr) && position == pos
  {
    position, Repr := pos, {this};
  }
  function method Brand(): string {
    "Fiat"
  }
  method Drive()
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures old(position) <= position
  {
    position := if position < 97 then position + 3 else 100;
  }
}

class Volvo extends Automobile {
  var odometer: Odometer
  predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr && odometer in Repr &&
    position % 10 == 0 &&  // position is always a multiple of 10
    odometer.value == position
  }
  constructor ()
    ensures Valid() && fresh(Repr)
  {
    position, Repr := 0, {this};
    odometer := new Odometer();
    Repr := Repr + {odometer};
  }
  function method Brand(): string {
    "Volvo"
  }
  method Drive()
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures old(position) < position  // always promises to make a move
  {
    position := position + 10;
    odometer.Advance(10);
  }
}

class Odometer {
  var value: int
  constructor ()
    ensures value == 0
  {
    value := 0;
  }
  method Advance(d: int)
    requires 0 <= d
    modifies this
    ensures value == old(value) + d
  {
    value := value + d;
  }
}

class Catacar extends Automobile {
  var f: Fiat
  var v: Volvo
  predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    f in Repr && this !in f.Repr && f.Repr <= Repr && f.Valid() &&
    v in Repr && this !in v.Repr && v.Repr <= Repr && v.Valid() &&
    f.Repr !! v.Repr &&
    position == f.position + v.position
  }
  constructor ()
    ensures Valid() && fresh(Repr)
  {
    var fiat := new Fiat(0);
    var volvo := new Volvo();
    f, v := fiat, volvo;
    Repr := {this} + fiat.Repr + volvo.Repr;
    position := volvo.position;
  }
  function method Brand(): string {
    "Catacar"
  }
  method Drive()
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures old(position) <= position
  {
    f := new Fiat(f.position);
    f.Drive();  v.Drive();
    Repr := Repr + v.Repr + f.Repr;
    position := f.position + v.position;
  }
}

method Main() {
  var auto: Automobile;
  auto := new Fiat(0);
  WorkIt(auto);
  auto := new Volvo();
  WorkIt(auto);
  auto := new Catacar();
  WorkIt(auto);
}

method WorkIt(auto: Automobile)
  requires auto.Valid()
  modifies auto.Repr
{
  auto.Drive();
  auto.Drive();
  assert old(auto.position) <= auto.position;
  print auto.Brand(), ": ", auto.position, "\n";
  auto.position := 18;  // note, this may destroy the automobile's consistency condition (given by Valid)
}
