
include "../../Test/libraries/src/JSON/Stacks.dfy"

module {:options "/functionSyntax:4"} MetaSeq {

  import opened Stacks

  datatype Seq<T> = Empty | Direct(a: seq<T>) | Concat(left: Seq<T>, right: Seq<T>, length: nat) {

    predicate Valid() {
      match this
      case Concat(left, right, length) => 
        && left.Valid()
        && right.Valid()
        && left.Length() + right.Length() == length
      case _ => true
    }

    function Length(): nat {
      match this
      case Empty => 0
      case Direct(a) => |a|
      case Concat(_, _, length) => length
    }

    function At(i: nat): T 
      requires Valid()
      requires i < Length()
    {
      Force()[i]
    }

    function Concatenate(s: Seq<T>): Seq<T> {
      Concat(this, s, Length() + s.Length())
    }

    method Slice(start: nat, end: nat) returns (s: Seq<T>)
      requires start <= end <= Length()

    function Value(): seq<T> 
      requires Valid()
      ensures |Value()| == Length()
    {
      match this
      case Empty => []
      case Direct(a) => a
      case Concat(left, right, _) => left.Value() + right.Value()
    }

    // TODO: {:memoize} should result in thread-safe lazy evaluation in each runtime
    function {:memoize} Force(): seq<T> 
      requires Valid()
    {
      Value()
    } by method {
      match this
      case Concat(left, right, length) => {
        var builder: SeqBuilder<T> := new SeqBuilder(length);
        var toVisit := new Stack<Seq<T>>(Empty);
        :- expect toVisit.Push(right);
        :- expect toVisit.Push(left);

        while (0 < toVisit.size) {
          // TODO: PopFast needs fixing on the json branch
          var next := toVisit.At(toVisit.size - 1);
          toVisit.PopFast(next);
          match next
          case Concat(nextLeft, nextRight, _) => {
            :- expect toVisit.Push(nextRight);
            :- expect toVisit.Push(nextLeft);
          }
          case _ => {
            builder.Append(next.Value());
          }
        }
        
        return builder.Value();
      }
      case _ => return Value();
    }
  }

  class SeqBuilder<T> {
    var s: seq<T>

    constructor(length: nat) 
      ensures Value() == []
    {
      s := [];
    }

    method Append(t: seq<T>) 
      modifies this
      ensures Value() == old(Value()) + t
    {
      s := s + t;
    }

    function Value(): seq<T> reads this {
      s
    }
  }
}