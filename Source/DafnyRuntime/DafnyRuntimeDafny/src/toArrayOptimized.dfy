
include "array.dfy"
include "frames.dfy"
include "sequence.dfy"

module {:options "/functionSyntax:4"} ToArrayOptimized {

  import opened Arrays
  import opened Frames
  import opened Sequences
  
  // ghost predicate AllDisjoint<T>(builder: ResizableArray<T>, e: Sequence<T>, stack: ResizableArray<Sequence<T>>)
  //   requires stack.Valid()
  //   reads builder, builder.Repr, e, e.Repr, stack, stack.Repr, set expr <- stack.Value() :: {expr} + expr.Repr
  // {
  //   var allValidatables := {builder, e, stack} + set expr <- stack.Value();
  //   PairwiseDisjoint(allValidatables)
  // }

  method AppendRecursive<T>(builder: ResizableArray<T>, e: Sequence<T>)
    requires e.Valid()
    requires builder.Valid()
    modifies builder.Repr
    decreases e.size
    ensures builder.ValidAndDisjoint()
    ensures e.Valid()
    ensures builder.Value() == old(builder.Value()) + e.Value();

  {
    if e is Concat<T> {
      var concat := e as Concat<T>;
      AppendRecursive(builder, concat.left);
      AppendRecursive(builder, concat.right);
    } else if e is Lazy<T> {
      var lazy := e as Lazy<T>;
      var boxed := lazy.exprBox.Get();
      AppendRecursive(builder, boxed);
    } else {
      var a: Direct<T> := e.ToArray();
      builder.Append(a.value);
    }
  }

  method {:tailrecursion} AppendOptimized<T>(builder: ResizableArray<T>, e: Sequence<T>, stack: ResizableArray<Sequence<T>>)
    requires e.Valid()
    requires builder.Valid()
    requires stack.Valid()
    requires builder.Repr !! stack.Repr;
    requires forall expr <- stack.Value() :: expr.Valid()
    modifies builder.Repr, stack.Repr
    decreases e.size + SizeSum(stack.Value())
    ensures builder.Valid()
    ensures stack.Valid()
    ensures e.Valid()
    ensures forall expr <- stack.Value() :: expr.Valid()
    ensures builder.Value() == old(builder.Value()) + e.Value() + ConcatValueOnStack(old(stack.Value()));
  {
    if e is Concat<T> {
      var concat := e as Concat<T>;
      LemmaConcatValueOnStackWithTip(stack.Value(), concat.right);
      stack.AddLast(concat.right);
      AppendOptimized(builder, concat.left, stack);
    } else if e is Lazy<T> {
      var lazy := e as Lazy<T>;
      var boxed := lazy.exprBox.Get();
      AppendOptimized(builder, boxed, stack);
    } else {
      var a: Direct<T> := e.ToArray();
      assert forall expr <- stack.Value() :: expr.Valid();
      builder.Append(a.value);
      assert forall expr <- stack.Value() :: expr.Valid();
      if 0 < stack.size {
        ghost var willBeNext := stack.Last();
        assert willBeNext in stack.Value();
        assert forall expr <- stack.Value() :: expr.Valid();
        var next: Sequence<T> := stack.RemoveLast();
        LemmaConcatValueOnStackWithTip(stack.Value(), next);
        assert next == willBeNext;
        assert stack.Value() == old(stack.Value()[..(stack.size - 1)]);
        assert forall expr <- stack.Value() :: expr in old(stack.Value());
        assert willBeNext == next;
        assert next in old(stack.Value());
        assert forall expr <- stack.Value() :: expr.Valid();

        assert next.size + SizeSum(stack.Value()) == old(SizeSum(stack.Value()));
        assert next.size + SizeSum(stack.Value()) < e.size + old(SizeSum(stack.Value()));

        AppendOptimized(builder, next, stack);
      }
    }

    assert builder.Value() == old(builder.Value()) + e.Value() + ConcatValueOnStack(old(stack.Value()));
  }

  ghost function ConcatValueOnStack<T>(s: seq<Sequence<T>>): seq<T>
    requires (forall e <- s :: e.Valid())
  {
    if |s| == 0 then
      []
    else
      s[|s| - 1].Value() + ConcatValueOnStack(s[..(|s| - 1)])
  }

  lemma LemmaConcatValueOnStackWithTip<T>(s: seq<Sequence<T>>, x: Sequence<T>) 
    requires (forall e <- s :: e.Valid())
    requires x.Valid()
    ensures ConcatValueOnStack(s + [x]) == x.Value() + ConcatValueOnStack(s)
  {
    // var valueFn := (e: Sequence<T>) reads e, e.Repr requires e.Valid() => e.Value();
    // calc {
    //   ConcatValueOnStack(s + [x]);
    //   Seq.Flatten(Seq.Map(valueFn, Seq.Reverse(s + [x])));
    //   { reveal Seq.Reverse(); }
    //   Seq.Flatten(Seq.Map(valueFn, [x] + Seq.Reverse(s)));
    //   { reveal Seq.Map(); }
    //   Seq.Flatten([x.Value()] + Seq.Map(valueFn, Seq.Reverse(s)));
    //   x.Value() + Seq.Flatten(Seq.Map(valueFn, Seq.Reverse(s)));
    //   x.Value() + ConcatValueOnStack(s);
    // }
  }

  ghost function SizeSum<T>(s: seq<Sequence<T>>): nat 
    requires forall e <- s :: e.Valid()
  {
    if |s| == 0 then 
      0 
    else
      var last := |s| - 1;
      SizeSum(s[..last]) + s[last].size
  }
}