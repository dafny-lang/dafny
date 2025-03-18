
module TerminationExample {

  import opened Std.Termination

  method Test() {
    reveal TerminationMetric.DecreasesTo();
    
    var tm := TMNat(7);
    var tm2 := TMNat(8);
    assert tm2.DecreasesTo(tm);

    assert TMComma(tm2, tm2).DecreasesTo(TMComma(tm, tm2));
    assert TMComma(tm2, tm2).DecreasesTo(TMComma(tm2, tm));
    assert !TMComma(tm, tm2).DecreasesTo(TMComma(tm2, tm));
  }

  // This isn't an example of using the Std.Termination module,
  // it's an illustration of why the `decreases to` relation
  // is defined the way it is on sequences,
  // with both elements of and subsequences of a sequence
  // considered lower than that sequence.

  datatype Tree<T> = Node(children: seq<Tree<T>>) | Nil

  function Count<T>(t: Tree<T>): nat {
    match t
    case Node(children) =>
      // assert t decreases to children;
      CountSum(children)
    case Nil =>
      0
  }

  function CountSum<T>(children: seq<Tree<T>>): nat {
    if |children| == 0 then
      0
    else
      assert children decreases to children[0];
      var firstCount := Count(children[0]);
      assert children decreases to children[1..];
      var restCount := CountSum(children[1..]);
      firstCount + restCount
  }
}