include "CompilerCommon.dfy"
include "Library.dfy"

module Values {
  import Lib.Math
  import opened Lib.Datatypes
  import DafnyCompilerCommon.AST.Exprs
  import DafnyCompilerCommon.AST.Types

  type Context = map<string, Value>

  datatype Value = 
    | Bool(b: bool)
    | Char(c: char)
    | Int(i: int)
    | Real(r: real)
    | BigOrdinal(o: ORDINAL)
    | BitVector(width: nat, value: int)
    | Map(m: map<Value, Value>)
    | Multiset(ms: multiset<Value>)
    | Seq(sq: seq<Value>)
    | Set(st: set<Value>)
    | Closure(ctx: Context, vars: seq<string>, body: Exprs.T)
  {
    predicate method HasType(ty: Types.T) {
      this.WellFormed1() &&
      match (this, ty) // FIXME tests on other side
        case (Bool(b), Bool()) => true
        case (Char(c), Char()) => true
        case (Int(i), Int()) => true
        case (Real(r), Real()) => true
        case (BigOrdinal(o), BigOrdinal()) => true
        case (BitVector(width, value), BitVector(twidth)) =>
          width == twidth
        case (Map(m), Collection(true, Map(kT), eT)) =>
          forall x | x in m :: x.HasType(kT) && m[x].HasType(eT)
        case (Multiset(ms), Collection(true, Multiset, eT)) =>
          forall x | x in ms :: x.HasType(eT)
        case (Seq(sq), Collection(true, Seq, eT)) =>
          forall x | x in sq :: x.HasType(eT)
        case (Set(st), Collection(true, Set, eT)) =>
          forall x | x in st :: x.HasType(eT)
        case (Closure(ctx, vars, body), Function(args, ret)) =>
          true // FIXME: Need a typing relation on terms, not just values

        // DISCUSS: Better way to write this?  Need exhaustivity checking
        case (Bool(b), _) => false
        case (Char(c), _) => false
        case (Int(i), _) => false
        case (Real(r), _) => false
        case (BigOrdinal(o), _) => false
        case (BitVector(width, value), _) => false
        case (Map(m), _) => false
        case (Multiset(ms), _) => false
        case (Seq(sq), _) => false
        case (Set(st), _) => false
        case (Closure(ctx, vars, body), _) => false
    }

    function method Children() : (cs: set<Value>)
      ensures forall c | c in cs :: c < this
    {
      match this
        case Bool(b) => {}
        case Char(c) => {}
        case Int(i) => {}
        case Real(r) => {}
        case BigOrdinal(o) => {}
        case BitVector(width, value) => {}
        case Map(m) => m.Values
        case Multiset(ms) => set x | x in ms
        case Seq(sq) => set x | x in sq
        case Set(st) => st
        case Closure(ctx, vars_, body_) => ctx.Values
    }

    // This duplicates a bit Types.WellFormed().
    // More specifically, if we have ``value.HasType(t)``, then we can deduce from the type well-formedness
    // that we also have ``value.WellFormed()``.
    predicate method WellFormed1() {
      match this {
        case BitVector(width, val) =>
          0 <= value < Math.IntPow(2, width)
        case _ => true
      }

/*      match this {
        case Bool(b) => true
        case Char(c) => true
        case Int(i) => true
        case Real(r) => true
        case BigOrdinal(o) => true
        case BitVector(width, val) =>
          0 <= value < Math.IntPow(2, width)
        case Map(m) =>
          && this.NoFunction()
          && (forall x | x in m :: x.WellFormed1() && m[x].WellFormed1())
        case Multiset(ms) =>
          && this.NoFunction()
          && (forall x | x in ms :: x.WellFormed1())
        case Seq(sq) =>
          && this.NoFunction()
          && (forall x | x in sq :: x.WellFormed1())
        case Set(st) =>
          && this.NoFunction()
          && (forall x | x in st :: x.WellFormed1())
        case Closure(ctx, vars, body) =>
          // TODO: is that enough?
          && (forall x | x in ctx :: ctx[x].WellFormed1())
      }*/
    }

    predicate method All(P: Value -> bool) {
      P(this) && forall c | c in this.Children() :: c.All(P)
    }

    lemma AllImpliesChildren(P: Value -> bool)
      requires All(P)
      ensures forall c | c in Children() :: c.All(P)
    {}

    function method Cast(ty: Types.T) : (v: Option<Value>)
      ensures v.Some? ==> HasType(ty)
    {
      if HasType(ty) then Some(this) else None
    }
  }

  type T = Value

  datatype TypedValue = Value(ty: Types.T, v: T) {
    predicate Wf() { v.HasType(ty) }
  }

  // FIXME how do we define the interpreter to support :| without committing to a single interpretation of :|?
  // NOTE: Maybe tag each syntactic :| with a distinct color and add the color somehow into the Dafny-side :| used to implement it.  Pro: it allows inlining.
}

type Value = Values.T
