
include "array.dfy"
include "frames.dfy"
include "sequence.dfy"

module {:options "/functionSyntax:4"} ToArrayOptimized {

  import opened Arrays
  import opened Frames
  import opened MetaSeq
  
  method {:tailrecursion} ToArrayOptimized<T>(builder: ResizableArray<T>, e: SeqExpr<T>, stack: ResizableArray<SeqExpr<T>>)
    requires e.Valid()
    requires builder.Valid()
    requires stack.Valid()
    requires builder.Repr !! stack.Repr !! e.Repr;
    requires forall e <- stack.Value() :: e.Repr !! stack.Repr
    requires forall expr <- stack.Value() :: builder.Repr !! expr.Repr !! e.Repr && expr.Valid()
    modifies builder.Repr, stack.Repr
    decreases e.Size() + SizeSum(stack.Value())
    ensures builder.Valid()
    ensures stack.Valid()
    ensures e.Valid()
    ensures forall expr <- stack.Value() :: expr.Valid()
    ensures builder.Value() == old(builder.Value()) + e.Value() + ConcatValueOnStack(old(stack.Value()));

  {
    if e is Concat<T> {
      var concat := e as Concat<T>;
      stack.AddLast(concat.right);
      ToArrayOptimized(builder, concat.left, stack);
    } else if e is Lazy<T> {
      var lazy := e as Lazy<T>;
      var boxed := AtomicBox<SeqExpr<T>>.Get(lazy.exprBox);
      assert boxed.Size() < lazy.Size();
      ToArrayOptimized(builder, boxed, stack);
    } else {
      var a := e.ToArray();
      assert forall expr <- stack.Value() :: expr.Valid();
      builder.Append(a);
      if 0 < stack.size {
        assert forall expr <- stack.Value() :: expr.Repr !! stack.Repr;
        var next: SeqExpr<T> := stack.RemoveLast();
        assert next in old(stack.Value());
        assert next.Repr !! stack.Repr;
        ToArrayOptimized(builder, next, stack);
      }
    }
  }

  ghost function ConcatValueOnStack<T>(s: seq<SeqExpr<T>>): seq<T>
    reads (set e <- s, o <- e.Repr :: o)
    requires (forall e <- s :: e.Valid())
  {
    if |s| == 0 then
      []
    else
      s[|s| - 1].Value() + ConcatValueOnStack(s[..(|s| - 1)])
  }

  lemma LemmaConcatValueOnStackWithTip<T>(s: seq<SeqExpr<T>>, x: SeqExpr<T>) 
    requires (forall e <- s :: e.Valid())
    requires x.Valid()
    ensures ConcatValueOnStack(s + [x]) == x.Value() + ConcatValueOnStack(s)
  {
    // var valueFn := (e: SeqExpr<T>) reads e, e.Repr requires e.Valid() => e.Value();
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

  ghost function SizeSum<T>(s: seq<SeqExpr<T>>): nat 
    reads set e <- s, o <- e.Repr :: o
    requires forall e <- s :: e.Valid()
  {
    if |s| == 0 then 
      0 
    else
      var last := |s| - 1;
      SizeSum(s[..last]) + s[last].Size()
  }
}