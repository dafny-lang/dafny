
include "array.dfy"
include "frames.dfy"
include "sequence.dfy"

module {:options "/functionSyntax:4"} ToArrayOptimized {

  import opened Arrays
  import opened Frames
  import opened Sequences
  
  method AppendRecursive<T>(builder: ResizableArray<T>, e: Sequence<T>)
    requires e.Valid()
    requires builder.Valid()
    modifies builder.Repr
    decreases e.size
    ensures builder.ValidAndDisjoint()
    ensures e.Valid()
    ensures builder.Value() == old(builder.Value()) + e.Value();

  {
    if e is ConcatSequence<T> {
      var concat := e as ConcatSequence<T>;
      AppendRecursive(builder, concat.left);
      AppendRecursive(builder, concat.right);
    } else if e is LazySequence<T> {
      var lazy := e as LazySequence<T>;
      var boxed := lazy.box.Get();
      AppendRecursive(builder, boxed);
    } else {
      var a: ImmutableArray<T> := e.ToArray();
      builder.Append(a);
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
    if e is ConcatSequence<T> {
      var concat := e as ConcatSequence<T>;
      stack.AddLast(concat.right);
      AppendOptimized(builder, concat.left, stack);
    } else if e is LazySequence<T> {
      var lazy := e as LazySequence<T>;
      var boxed := lazy.box.Get();
      AppendOptimized(builder, boxed, stack);
    } else {
      var a := e.ToArray();
      builder.Append(a);
      if 0 < stack.size {
        var next: Sequence<T> := stack.RemoveLast();
        AppendOptimized(builder, next, stack);
      }
    }
  }

  ghost function ConcatValueOnStack<T>(s: seq<Sequence<T>>): seq<T>
    requires (forall e <- s :: e.Valid())
  {
    if |s| == 0 then
      []
    else
      s[|s| - 1].Value() + ConcatValueOnStack(s[..(|s| - 1)])
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