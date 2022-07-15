
include "../../Test/libraries/src/Math.dfy"

module {:options "/functionSyntax:4"} MetaSeq {

  import Math

  datatype SeqExpr<T> = 
    | Empty
    | Direct(a: seq<T>)
    | Concat(left: SeqExpr<T>, right: SeqExpr<T>, length: nat)
    | Lazy(ghost value: seq<T>, ghost boxDepth: nat, exprBox: AtomicBox<SeqExpr<T>>, length: nat) 
  {
    ghost predicate Valid()
      decreases Depth(), 0
    {
      match this
      case Concat(left, right, length) => 
        && left.Valid()
        && right.Valid()
        && left.Length() + right.Length() == length
      case Lazy(value, depth, exprBox, length) => 
        && length == |value|
        && exprBox.inv == ((e: SeqExpr<T>) => e.Depth() < depth && e.Valid() && e.Value() == value)
      case _ => true
    }

    ghost function Depth(): nat {
      match this {
        case Concat(left, right, _) => 1 + Math.Max(left.Depth(), right.Depth())
        case Lazy(_, depth, _, _) => depth
        case _ => 0
      }
    }

    ghost function NodeCount(): nat {
      match this {
        case Concat(left, right, _) => 1 + left.NodeCount() + right.NodeCount()
        case _ => 1
      }
    }

    function Length(): nat {
      match this
      case Empty => 0
      case Direct(a) => |a|
      case Concat(_, _, length) => length
      case Lazy(_, _, _, length) => length
    }

    function At(i: nat): T 
      requires Valid()
      requires i < Length()
    {
      Value()[i]
    }

    function Concatenate(s: SeqExpr<T>): SeqExpr<T> {
      Concat(this, s, Length() + s.Length())
    }

    function Value(): seq<T> 
      requires Valid()
      decreases Depth(), 2
      ensures |Value()| == Length()
    {
      match this
      case Empty => []
      case Direct(a) => a
      case Concat(left, right, length) => left.Value() + right.Value()
      case Lazy(value, _, _, _) => value
    } by method {
      match this
      case Empty => return [];
      case Direct(a) => return a;
      case Concat(left, right, length) => {
        var builder := new SeqBuilder<T>(length);
        AppendValue(builder);
        return builder.Value();
      }
      case Lazy(_, _, seqExpr, _) => {
        var expr := exprBox.Get();
        var value := expr.Value();
        exprBox.Put(Direct(value));
        return value;
      }
    }

    method AppendValue(builder: SeqBuilder<T>) 
      requires Valid()
      modifies builder
      decreases Depth()
      ensures builder.Value() == old(builder.Value()) + Value();
    {
      match this {
        case Empty =>
        case Direct(a) => {
          builder.Append(a);
        }
        case Concat(left, right, _) => {
          left.AppendValue(builder);
          right.AppendValue(builder);
        }
        case Lazy(value, _, _, _) => {
          var expr := exprBox.Get();
          expr.AppendValue(builder);
        }
      }
    }
  }

  // TODO: Make this an extern. How to monomorphize?
  class SeqBuilder<T> {
    var value: seq<T>

    constructor(length: nat) 
      ensures Value() == []
    {
      value := [];
    }

    method Append(t: seq<T>) 
      modifies this
      ensures Value() == old(Value()) + t
    {
      value := value + t;
    }

    function Value(): seq<T> reads this {
      value
    }
  }

  class {:extern} AtomicBox<T> {
    ghost const inv: T -> bool

    constructor(ghost inv: T -> bool, t: T)
      requires inv(t)
      ensures this.inv == inv

    method Put(t: T)
      requires inv(t)

    method Get() returns (t: T)
      ensures inv(t)
  }
}