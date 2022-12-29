// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node<T> {
  ghost var List: seq<T>
  ghost var Repr: set<Node<T>>

  var data: T
  var next: Node?<T>

  predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    (next == null ==> List == [data]) &&
    (next != null ==>
        next in Repr && next.Repr <= Repr &&
        this !in next.Repr &&
        List == [data] + next.List &&
        next.Valid())
  }

  constructor (d: T)
    ensures Valid() && fresh(Repr)
    ensures List == [d]
  {
    data, next := d, null;
    List, Repr := [d], {this};
  }

  constructor InitAsPredecessor(d: T, succ: Node<T>)
    requires succ.Valid()
    ensures Valid() && fresh(Repr - succ.Repr);
    ensures List == [d] + succ.List;
  {
    data, next := d, succ;
    List := [d] + succ.List;
    Repr := {this} + succ.Repr;
  }

  method Prepend(d: T) returns (r: Node<T>)
    requires Valid()
    ensures r.Valid() && fresh(r.Repr - old(Repr))
    ensures r.List == [d] + List
  {
    r := new Node.InitAsPredecessor(d, this);
  }

	method Print()
		requires Valid()
		decreases |List|
	{
		print data, " ";
		if next != null {
			next.Print();
		}
	}
}

method Main()
{
	var l2 := new Node(2);
  var l1 := l2.Prepend(1);
	l1.Print();
  print "\n";
}
