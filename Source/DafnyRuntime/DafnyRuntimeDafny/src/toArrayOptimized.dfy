
include "array.dfy"
include "frames.dfy"
include "sequence.dfy"

module {:options "/functionSyntax:4"} ToArrayOptimized {

  import opened Arrays
  import opened Frames
  import opened MetaSeq
  
  // ghost predicate AllDisjoint<T>(builder: ResizableArray<T>, e: SeqExpr<T>, stack: ResizableArray<SeqExpr<T>>)
  //   requires stack.Valid()
  //   reads builder, builder.Repr, e, e.Repr, stack, stack.Repr, set expr <- stack.Value() :: {expr} + expr.Repr
  // {
  //   var allValidatables := {builder, e, stack} + set expr <- stack.Value();
  //   PairwiseDisjoint(allValidatables)
  // }

  method {:tailrecursion} ToArrayOptimized<T>(builder: ResizableArray<T>, e: SeqExpr<T>, stack: ResizableArray<SeqExpr<T>>)
    requires e.Valid()
    requires builder.Valid()
    requires stack.Valid()
    requires builder.Repr !! stack.Repr !! e.Repr;
    requires forall i, j | 0 <= i < j < stack.size :: 
      var first := stack.Value()[i];
      var second := stack.Value()[j];
      first != second && first.Repr !! second.Repr
    requires forall expr <- stack.Value() :: stack.Repr !! builder.Repr !! expr.Repr !! e.Repr && expr.Valid()
    modifies builder.Repr, stack.Repr
    decreases e.Size() + SizeSum(stack.Value())
    // ensures builder.Valid()
    // ensures stack.Valid()
    // ensures e.Valid()
    // ensures forall expr <- stack.Value() :: expr.Valid()
    // ensures builder.Value() == old(builder.Value()) + e.Value() + ConcatValueOnStack(old(stack.Value()));

  {
    // if e is Concat<T> {
    //   var concat := e as Concat<T>;
    //   stack.AddLast(concat.right);
    //   ToArrayOptimized(builder, concat.left, stack);
    // } else if e is Lazy<T> {
    //   var lazy := e as Lazy<T>;
    //   var boxed := AtomicBox<SeqExpr<T>>.Get(lazy.exprBox);
    //   ToArrayOptimized(builder, boxed, stack);
    // } else {
      var a := e.ToArray();
      assert forall expr <- stack.Value() :: expr.Valid();
      builder.Append(a);
      assert forall expr <- stack.Value() :: unchanged(expr.Repr);
      assert forall expr <- stack.Value() :: expr.Valid();
      if 0 < stack.size {
        ghost var willBeNext := stack.Last();
        assert willBeNext in stack.Value();
        assert forall expr <- stack.Value() :: expr.Repr !! stack.Repr;
        assert forall expr <- stack.Value() :: expr.Valid();
        assert willBeNext.Repr !! stack.Repr;
        assert forall expr <- stack.Value()[..(stack.size - 1)] :: willBeNext != expr && willBeNext.Repr !! expr.Repr;
        assert forall expr <- stack.Value(), expr' <- stack.Value() | expr != expr' :: expr.Repr !! expr'.Repr;
        var next: SeqExpr<T> := stack.RemoveLast();
        assert next == willBeNext;
        assert stack.Value() == old(stack.Value()[..(stack.size - 1)]);
        assert forall expr <- stack.Value() :: next != expr && next.Repr !! expr.Repr;
        assert unchanged(next.Repr);
        assert forall expr <- stack.Value() :: expr in old(stack.Value());
        assert forall expr <- stack.Value() :: unchanged(expr.Repr);
        assert willBeNext == next;
        assert next in old(stack.Value());
        assert next.Repr !! stack.Repr;
        assert forall expr <- stack.Value() :: expr.Valid();
        assert old(SizeSum(stack.Value())) == next.Size() + SizeSum(stack.Value());
        assert stack.Repr !! builder.Repr !! next.Repr;
        assert forall expr <- stack.Value() :: builder.Repr !! expr.Repr;
        
        assert forall expr <- stack.Value() :: stack.Repr !! expr.Repr;
        ToArrayOptimized(builder, next, stack);
      }
    // }
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