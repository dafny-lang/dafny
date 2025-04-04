
module TerminationExample {

  import opened Std.Termination
  import opened Std.Ordinal

  @ResourceLimit("1e7")
  @IsolateAssertions
  method Test() {
    var tm := TMNat(7);
    var tm2 := TMNat(8);
    assert tm2.Ordinal() > tm.Ordinal() by {
      reveal TerminationMetric.Ordinal();
    }

    var s1 := TMSeq([TMNat(1), TMNat(2), TMNat(3)]);
    var s2 := TMSeq([TMNat(2), TMNat(3)]);
    var s3 := TMSeq([TMNat(1), TMNat(2)]);
    var s4 := TMSeq([TMNat(1), TMNat(3)]);
    assert s1.seqValue[1..] == s2.seqValue;
    s1.SeqDecreasesToProperSuffix(s2, 1);
    assert s1.seqValue[..2] == s3.seqValue;
    s1.SeqDecreasesToProperPrefix(s3, 2);
    assert s1.seqValue[..1] + s1.seqValue[2..] == s4.seqValue;
    s1.SeqDecreasesToProperDeletion(s4, 1, 2);
  }

  method {:test} TupleTest() {
    reveal TerminationMetric.Ordinal();

    var tm := TMNat(7);
    var tm2 := TMNat(8);
    assert tm2.Ordinal() > tm.Ordinal();

    TMTuple(TMTop, tm2, tm2).TupleDecreasesToTuple(TMTuple(TMTop, tm, tm2));
    assert TMTuple(TMTop, tm2, tm2).Ordinal() > TMTuple(TMTop, tm, tm2).Ordinal();
    TMTuple(TMTop, tm2, tm2).TupleDecreasesToTuple(TMTuple(TMTop, tm2, tm));
    assert TMTuple(TMTop, tm2, tm2).Ordinal() > TMTuple(TMTop, tm2, tm).Ordinal();

    // Can't be verified
    // assert (Tuple(Omega(), tm, tm2).Ordinal() > Tuple(Omega(), tm2, tm).Ordinal());
  }

  method {:test} Child() {
    var x: nat := 10;
    var child := TMNat(x);
    var parent := TMSeq([child]);
    assert parent.Ordinal() > child.Ordinal() by {
      reveal TerminationMetric.Ordinal();
    }
  }

  method {:test} Succ() {
    reveal TerminationMetric.Ordinal();
    assert forall x: TerminationMetric :: TMSucc(x).DecreasesTo(TMNat(0));
  }

  method {:test} NestedLoop() {
    reveal TerminationMetric.Ordinal();
    var x: nat := 10;
    var y: nat := 10;
    var tm := TMTuple(TMTop, TMNat(x), TMNat(y));
    while 0 < x || 0 < y
      invariant tm == TMTuple(TMTop, TMNat(x), TMNat(y))
      decreases tm.Ordinal()
    {
      ghost var tmBefore := tm;
      ghost var yBefore := y;
      if y == 0 {
        if x == 0 {
          break;
        } else {
          x := x - 1;
          y := 10;

          tm := TMTuple(TMTop, TMNat(x), TMNat(y));
          tmBefore.TupleDecreasesToTuple(tm);
        }
      } else {
        y := y - 1;

        tm := TMTuple(TMTop, TMNat(x), TMNat(y));
        tmBefore.TupleDecreasesToTuple(tm);
      }
    }
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
      assert t decreases to children;
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