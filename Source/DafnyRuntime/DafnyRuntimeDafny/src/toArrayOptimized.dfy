
include "array.dfy"
include "frames.dfy"
include "sequence.dfy"

module {:options "/functionSyntax:4"} ToArrayOptimized {

  import opened Arrays
  import opened Frames
  import opened MetaSeq
  
  method ToArrayOptimized<T>(e: Concat<T>) returns (ret: ResizableArray<T>)
    requires e.Valid()
    ensures ret.Valid()
    ensures ret.Value() == e.Value()
  {
    var builder := new ResizableArray<T>(e.length);
    var stack := new ResizableArray<SeqExpr<T>>(10);
    stack.AddLast(e);
    // assert stack.Value() == [e];
    // LemmaConcatValueOnStackWithTip([], e);
    // assert ConcatValueOnStack(stack.Value()) == e.Value();
    while 0 < stack.size 
      invariant stack.Valid()
      // invariant PairwiseDisjoint({builder as Validatable, stack as Validatable} + (set v: Validatable <- stack.Value()))
      invariant builder.Valid()
      invariant fresh(builder.Repr)
      invariant fresh(stack.Repr)
      invariant forall e <- stack.Value() :: e.Valid()
      invariant builder.Value() + ConcatValueOnStack(stack.Value()) == e.Value()
      decreases if 0 < stack.size then stack.Last().Size() else 0, SizeSum(stack.Value())
    {
      var next: SeqExpr<T> := stack.RemoveLast();
      if next is Concat<T> {
        var concat := next as Concat<T>;
        // ghost var stackBefore := stack.Value();
        stack.AddLast(concat.right);
        // LemmaConcatValueOnStackWithTip(stackBefore, concat.right);
        // ghost var stackInbetween := stack.Value();
        stack.AddLast(concat.left);
        // LemmaConcatValueOnStackWithTip(stackInbetween, concat.left);
      } else if next is Lazy<T> {
        var lazy := next as Lazy<T>;
        var boxed := lazy.exprBox.Get();
        stack.AddLast(boxed);
      } else {
        var a := next.ToArray();
        builder.Append(a);
      }
    }
    return builder;
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