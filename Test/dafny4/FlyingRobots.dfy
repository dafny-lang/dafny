// RUN: %dafny /compile:3 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The flying robots examples from an F* tutorial.  It demonstrates how to specify
// mutable data structures in the heap.

class Cell {
  var val:int
  constructor (v:int)
    ensures val == v
  {
    val := v;
  }
}

class Point {
  ghost var Value: (int, int, int)

  ghost var Repr: set<object>
  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    {x,y,z} <= Repr &&
    x != y && y != z && z != x &&
    Value == (x.val, y.val, z.val)
  }

  var x:Cell, y:Cell, z:Cell

  constructor (a:int, b:int, c:int)
    ensures Valid() && fresh(Repr)
    ensures Value == (a, b, c)
  {
    x := new Cell(a);
    y := new Cell(b);
    z := new Cell(c);
    Repr := {this, x, y, z};
    Value := (a, b, c);
  }

  method Mutate(a:int, b:int, c:int)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Value == (a, b, c)
  {
    x.val, y.val, z.val := a, b, c;
    Value := (a, b, c);
  }
}

class Arm {
  ghost var Value: (int, int)

  ghost var Repr: set<object>
  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    {polar, azim} <= Repr &&
    polar != azim &&
    Value == (polar.val, azim.val)
  }

  var polar:Cell
  var azim:Cell

  constructor (polar_in:int, azim_in:int)
    ensures Valid() && fresh(Repr)
    ensures Value == (polar_in, azim_in)
  {
    polar := new Cell(polar_in);
    azim := new Cell(azim_in);
    Repr := {this, polar, azim};
    Value := (polar_in, azim_in);
  }

  method Mutate(polar_in:int, azim_in:int)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Value == (polar_in, azim_in)
  {
    polar.val, azim.val := polar_in, azim_in;
    Value := (polar_in, azim_in);
  }
}

class Bot {
  ghost var Repr: set<object>
  ghost predicate {:opaque} Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    pos in Repr && {left, right} <= Repr &&
    left != right &&
    pos.Repr <= Repr && left.Repr <= Repr && right.Repr <= Repr &&
    pos.Repr !! left.Repr !! right.Repr &&
    pos.Valid() && left.Valid() && right.Valid()
  }

  var pos:Point
  var left:Arm
  var right:Arm

  constructor ()
    ensures Valid() && fresh(Repr)
  {
    pos := new Point(0, 0, 0);
    left := new Arm(0, 0);
    right := new Arm(0, 0);
    new;
    Repr := {this} + pos.Repr + left.Repr + right.Repr;
    reveal Valid();
  }

  ghost predicate flying()
    requires (reveal Valid(); Valid())
    reads Repr
  {
    pos.z.val > 0
  }

  ghost predicate arms_up()
    requires (reveal Valid(); Valid())
    reads Repr
  {
    left.polar.val == right.polar.val == 0
  }

  ghost predicate robot_inv()
    requires (reveal Valid(); Valid())
    reads Repr
  {
    flying() ==> arms_up()
  }

  method Fly()
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures robot_inv() && flying()
  {
    reveal Valid();
    left.polar.val, right.polar.val := 0, 0;
    pos.z.val := 100;
    right.azim.val := 17;
    pos.Value := (pos.Value.0, pos.Value.1, 100);
    left.Value, right.Value := (0, left.Value.1), (0, 17);
    reveal Valid();
  }
}

// This method tests that Fly operates independently on disjoint robots
method FlyRobots(b0:Bot, b1:Bot)
  requires b0.Valid()
  requires b1.Valid()
  requires b0 != b1 ==> b0.Repr !! b1.Repr
  modifies b0.Repr, b1.Repr
  ensures b0.Valid() && fresh(b0.Repr - old(b0.Repr))
  ensures b1.Valid() && fresh(b1.Repr - old(b1.Repr))
  ensures b0 != b1 ==> b0.Repr !! b1.Repr
  ensures  b0.robot_inv() && b1.robot_inv()
  ensures  b0.flying() && b1.flying()
{
  b0.Fly();
  b1.Fly();
}

// ----- robot armies ----------

// The union of .Repr for the robots in "bots"
ghost function ArmyRepr(bots:seq<Bot>) : set<object>
  reads set b | b in bots
{
  set b,o | b in bots && o in b.Repr :: o
}

// An army is a sequence of disjoint, valid robots
ghost predicate ValidArmy(bots:seq<Bot>)
  reads set b | b in bots
  reads ArmyRepr(bots)
{
      (forall i :: 0 <= i < |bots| ==> bots[i].Valid())
  &&  (forall i,j :: 0 <= i < j < |bots| ==> bots[i].Repr !! bots[j].Repr)
}

method FlyRobotArmy(bots:seq<Bot>)
  requires ValidArmy(bots)
  modifies ArmyRepr(bots)
  ensures ValidArmy(bots) && fresh(ArmyRepr(bots) - old(ArmyRepr(bots)))
  ensures forall b :: b in bots ==> b.Valid() && b.robot_inv() && b.flying()
{
  if * {
    // fly recursively
    FlyRobotArmy_Recursively(bots);
  } else {
    // fly iteratively
    var n := 0;
    while n < |bots|
      invariant 0 <= n <= |bots|
      invariant ValidArmy(bots)
      invariant forall j :: 0 <= j < n ==> bots[j].Valid() && bots[j].robot_inv() && bots[j].flying()
      invariant forall i :: 0 <= i < |bots| ==> fresh(bots[i].Repr - old(bots[i].Repr))
    {
      FlyOne(bots, n);
      n := n + 1;
    }
  }
}

method FlyRobotArmy_Recursively(bots:seq<Bot>)
  requires ValidArmy(bots)
  modifies ArmyRepr(bots)
  ensures ValidArmy(bots)
  ensures forall i :: 0 <= i < |bots| ==> fresh(bots[i].Repr - old(bots[i].Repr))
  ensures forall b :: b in bots ==> b.robot_inv() && b.flying()
{
  if bots != [] {
    FlyOne(bots, 0);
    FlyRobotArmy_Recursively(bots[1..]);
  }
}

// This method is intended to be called in each loop iteration of FlyRobotArmy
method FlyOne(bots:seq<Bot>, n:int)
  requires 0 <= n < |bots|
  requires forall j :: 0 <= j < |bots| ==> bots[j].Valid()
  requires forall i,j :: 0 <= i < j < |bots| ==> bots[i].Repr !! bots[j].Repr
  requires forall j :: 0 <= j < n ==>  bots[j].robot_inv() && bots[j].flying()
  modifies bots[n].Repr
  ensures forall j :: 0 <= j < |bots| ==> bots[j].Valid()
  ensures fresh(bots[n].Repr - old(bots[n].Repr))
  ensures bots[n].robot_inv() && bots[n].flying()
  ensures forall j :: 0 <= j < |bots| && j != n ==> bots[j].Repr == old(bots[j].Repr)
  ensures forall j :: 0 <= j < n ==> bots[j].robot_inv() && bots[j].flying()
{
  bots[n].Fly();
}

// This method makes sure FlyRobotArmy is callable and callable again
method FormArmy(b0:Bot, b1:Bot, b2:Bot)
  requires b0.Valid() && b1.Valid() && b2.Valid()
  requires b0.Repr !! b1.Repr !! b2.Repr
  modifies b0.Repr, b1.Repr, b2.Repr
  ensures b0.Valid() && b1.Valid() && b2.Valid()
  ensures b0.Repr !! b1.Repr !! b2.Repr
  ensures fresh(b0.Repr + b1.Repr + b2.Repr - old(b0.Repr + b1.Repr + b2.Repr))
{
  var army := [b0, b1, b2];
  ArmyRepr3(army);
  FlyRobotArmy(army);
  FlyRobotArmy(army);  // do it again
  ArmyRepr3(army);
}

lemma ArmyRepr3(army:seq<Bot>)
  requires |army| == 3
  ensures ArmyRepr(army) == army[0].Repr + army[1].Repr + army[2].Repr
{
}

// ----- Make sure everything is callable ----------

method Main()
{
  var b0 := new Bot();
  var b1 := new Bot();
  FlyRobots(b0, b1);
  FlyRobots(b0, b1);
  FlyRobots(b1, b0);

  var b2 := new Bot();
  FormArmy(b0, b1, b2);
  FormArmy(b2, b0, b1);
}
