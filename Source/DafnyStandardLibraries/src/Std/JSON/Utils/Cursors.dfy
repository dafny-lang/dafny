/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**
 Implements slices augmented with an inner pointer tracking a position.
 */
module Std.JSON.Utils.Cursors {
  import opened BoundedInts
  import opened Wrappers
  import opened Vs = Views.Core
  import opened Lx = Lexers.Core

  datatype Split<+T> = SP(t: T, cs: FreshCursor) {
    ghost predicate BytesSplitFrom?(cs0: Cursor, spec: T -> bytes) {
      cs0.Bytes() == spec(t) + cs.Bytes()
    }

    ghost predicate SplitFrom?(cs0: Cursor, spec: T -> bytes) {
      cs.SplitFrom?(cs0) && BytesSplitFrom?(cs0, spec)
    }

    ghost predicate StrictlySplitFrom?(cs0: Cursor, spec: T -> bytes) {
      cs.StrictlySplitFrom?(cs0) && BytesSplitFrom?(cs0, spec)
    }
  }

  // LATER: Make this a newtype and put members here instead of requiring `Valid?` everywhere
  type Cursor = ps: Cursor_ | ps.Valid?
    witness Cursor([], 0, 0, 0)
  type FreshCursor = ps: Cursor | ps.BOF?
    witness Cursor([], 0, 0, 0)

  datatype CursorError<+R> =
    | EOF
    | ExpectingByte(expected: byte, b: opt_byte)
    | ExpectingAnyByte(expected_sq: seq<byte>, b: opt_byte)
    | OtherError(err: R)
  { // TODO: Include positions in errors
    function ToString(pr: R -> string) : string {
      match this
      case EOF => "Reached EOF"
      case ExpectingByte(b0, b) =>
        var c := if b > 0 then "'" + [b as char] + "'" else "EOF";
        "Expecting '" + [b0 as char] + "', read " + c
      case ExpectingAnyByte(bs0, b) =>
        var c := if b > 0 then "'" + [b as char] + "'" else "EOF";
        var c0s := seq(|bs0|, idx requires 0 <= idx < |bs0| => bs0[idx] as char);
        "Expecting one of '" + c0s + "', read " + c
      case OtherError(err) => pr(err)
    }
  }
  type CursorResult<+R> = Result<Cursor, CursorError<R>>

  datatype Cursor_ = Cursor(s: bytes, beg: uint32, point: uint32, end: uint32) {
    ghost const Valid?: bool :=
      0 <= beg as int <= point as int <= end as int <= |s| < TWO_TO_THE_32

    const BOF? :=
      point == beg

    const EOF? :=
      point == end

    static function OfView(v: View) : FreshCursor {
      Cursor(v.s, v.beg, v.beg, v.end)
    }

    static function OfBytes(bs: bytes) : FreshCursor
      requires |bs| < TWO_TO_THE_32
    {
      Cursor(bs, 0, 0, |bs| as uint32)
    }

    function Bytes() : bytes
      requires Valid?
    {
      s[beg..end]
    }

    ghost predicate StrictlyAdvancedFrom?(other: Cursor): (b: bool)
      requires Valid?
      ensures b ==>
                SuffixLength() < other.SuffixLength()
      ensures b ==>
                beg == other.beg && end == other.end ==>
                  forall idx | beg <= idx < point :: s[idx] == other.s[idx]
    {
      && s == other.s
      && beg == other.beg
      && end == other.end
      && point > other.point
    }

    ghost predicate AdvancedFrom?(other: Cursor)
      requires Valid?
    {
      || this == other
      || StrictlyAdvancedFrom?(other)
    }

    ghost predicate StrictSuffixOf?(other: Cursor)
      requires Valid?
      ensures StrictSuffixOf?(other) ==>
                Length() < other.Length()
    {
      && s == other.s
      && beg > other.beg
      && end == other.end
    }

    ghost predicate SuffixOf?(other: Cursor)
      requires Valid?
    {
      || this == other
      || StrictSuffixOf?(other)
    }

    ghost predicate StrictlySplitFrom?(other: Cursor)
      requires Valid?
    {
      && BOF?
      && StrictSuffixOf?(other)
    }

    ghost predicate SplitFrom?(other: Cursor)
      requires Valid?
    {
      || this == other
      || StrictlySplitFrom?(other)
    }

    function Prefix() : View requires Valid? {
      View(s, beg, point)
    }

    function Suffix() : Cursor requires Valid? {
      this.(beg := point)
    }

    function Split() : (sp: Split<View>) requires Valid?
      ensures sp.SplitFrom?(this, (v: View) => v.Bytes())
      ensures beg != point ==> sp.StrictlySplitFrom?(this, (v: View) => v.Bytes())
      ensures !BOF? ==> (sp.StrictlySplitFrom?(this, (v: View) => v.Bytes()) && sp.cs.StrictSuffixOf?(this))
      ensures !EOF? <==> !sp.cs.EOF?
    {
      SP(this.Prefix(), this.Suffix())
    }

    function PrefixLength() : uint32 requires Valid? {
      point - beg
    }

    function SuffixLength() : uint32 requires Valid? {
      end - point
    }

    function Length() : uint32 requires Valid? {
      end - beg
    }

    lemma PrefixSuffixLength()
      requires Valid?
      ensures Length() == PrefixLength() + SuffixLength()
    {}

    ghost predicate ValidIndex?(idx: uint32) {
      beg as int + idx as int < end as int
    }

    function At(idx: uint32) : byte
      requires Valid?
      requires ValidIndex?(idx)
    {
      s[beg + idx]
    }

    ghost predicate ValidSuffixIndex?(idx: uint32) {
      point as int + idx as int < end as int
    }

    function SuffixAt(idx: uint32) : byte
      requires Valid?
      requires ValidSuffixIndex?(idx)
    {
      s[point + idx]
    }

    function Peek(): (r: opt_byte)
      requires Valid?
      ensures r < 0 <==> EOF?
    {
      if EOF? then -1
      else SuffixAt(0) as opt_byte
    }

    predicate LookingAt(c: char): (b: bool)
      requires Valid?
      requires c as int < 256
      ensures b <==> !EOF? && SuffixAt(0) == c as byte
    {
      Peek() == c as opt_byte
    }

    function Skip(n: uint32): (ps: Cursor)
      requires Valid?
      requires point as int + n as int <= end as int
      ensures n == 0 ==> ps == this
      ensures n > 0 ==> ps.StrictlyAdvancedFrom?(this)
    {
      this.(point := point + n)
    }

    function Unskip(n: uint32): Cursor
      requires Valid?
      requires beg as int <= point as int - n as int
    {
      this.(point := point - n)
    }

    function Get<R>(err: R): (ppr: CursorResult<R>)
      requires Valid?
      ensures ppr.Success? ==> ppr.value.StrictlyAdvancedFrom?(this)
    {
      if EOF? then Failure(OtherError(err))
      else Success(Skip(1))
    }

    function AssertByte<R>(b: byte): (pr: CursorResult<R>)
      requires Valid?
      ensures pr.Success? ==> !EOF?
      ensures pr.Success? ==> s[point] == b
      ensures pr.Success? ==> pr.value.StrictlyAdvancedFrom?(this)
    {
      var nxt := Peek();
      if nxt == b as opt_byte then Success(Skip(1))
      else Failure(ExpectingByte(b, nxt))
    }

    @TailRecursion
    function AssertBytes<R>(bs: bytes, offset: uint32 := 0): (pr: CursorResult<R>)
      requires Valid?
      requires |bs| < TWO_TO_THE_32
      requires offset <= |bs| as uint32
      requires forall b | b in bs :: b as int < 256
      decreases SuffixLength()
      ensures pr.Success? ==> pr.value.AdvancedFrom?(this)
      ensures pr.Success? && offset < |bs| as uint32 ==> pr.value.StrictlyAdvancedFrom?(this)
      ensures pr.Success? ==> s[point..pr.value.point] == bs[offset..]
    {
      if offset == |bs| as uint32 then Success(this)
      else
        var ps :- AssertByte(bs[offset] as byte);
        ps.AssertBytes(bs, offset + 1)
    }

    function AssertChar<R>(c0: char): (pr: CursorResult<R>)
      requires Valid?
      requires c0 as int < 256
      ensures pr.Success? ==> pr.value.StrictlyAdvancedFrom?(this)
    {
      AssertByte(c0 as byte)
    }

    function SkipByte(): (ps: Cursor)
      requires Valid?
      decreases SuffixLength()
      ensures ps.AdvancedFrom?(this)
      ensures !EOF? ==> ps.StrictlyAdvancedFrom?(this)
    {
      if EOF? then this
      else Skip(1)
    }

    function SkipIf(p: byte -> bool): (ps: Cursor)
      requires Valid?
      decreases SuffixLength()
      ensures ps.AdvancedFrom?(this)
      ensures !EOF? && p(SuffixAt(0)) ==> ps.StrictlyAdvancedFrom?(this)
    {
      if EOF? || !p(SuffixAt(0)) then this
      else Skip(1)
    }

    function SkipWhile(p: byte -> bool): (ps: Cursor)
      requires Valid?
      decreases SuffixLength()
      ensures ps.AdvancedFrom?(this)
      ensures forall idx | point <= idx < ps.point :: p(ps.s[idx])
    {
      if EOF? || !p(SuffixAt(0)) then this
      else Skip(1).SkipWhile(p)
    } by method {
      var point' := this.point;
      var end := this.end;
      while point' < end && p(this.s[point'])
        // BUG(https://github.com/dafny-lang/dafny/issues/4847)
        invariant var thisAfter := this.(point := point'); thisAfter.Valid?
        invariant var thisAfter := this.(point := point'); thisAfter.SkipWhile(p) == this.SkipWhile(p)
      {
        point' := point' + 1;
      }
      return Cursor(this.s, this.beg, point', this.end);
    }

    function SkipWhileLexer<A, R>(step: Lexer<A, R>, st: A)
      : (pr: CursorResult<R>)
      requires Valid?
      decreases SuffixLength()
      ensures pr.Success? ==> pr.value.AdvancedFrom?(this)
    {
      match step(st, Peek())
      case Accept => Success(this)
      case Reject(err) => Failure(OtherError(err))
      case Partial(st) =>
        if EOF? then Failure(EOF)
        else Skip(1).SkipWhileLexer(step, st)
    } by method {
      var point' := point;
      var end := this.end;
      var st' := st;
      while true
        // BUG(https://github.com/dafny-lang/dafny/issues/4847)
        invariant var thisAfter := this.(point := point'); thisAfter.Valid?
        invariant var thisAfter := this.(point := point'); thisAfter.SkipWhileLexer(step, st') == this.SkipWhileLexer(step, st)
        decreases var thisAfter := this.(point := point'); thisAfter.SuffixLength()
      {
        var eof := point' == end;
        var minusone: opt_byte := -1; // BUG(https://github.com/dafny-lang/dafny/issues/2191)
        var c := if eof then minusone else this.s[point'] as opt_byte;
        match step(st', c)
        case Accept => return Success(Cursor(this.s, this.beg, point', this.end));
        case Reject(err) => return Failure(OtherError(err));
        case Partial(st'') =>
          if eof { return Failure(EOF); }
          else { st' := st''; point' := point' + 1; }
      }
    }
  }
}