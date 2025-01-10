/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**
 Implements byte strings whose bounds are representable as `int32` native integers (`View`s).
 */
module Std.JSON.Utils.Views.Core {
  import opened BoundedInts

  type View = v: View_ | v.Valid? witness View([], 0, 0)
  datatype View_ = View(s: bytes, beg: uint32, end: uint32) {
    ghost const Valid?: bool :=
      0 <= beg as int <= end as int <= |s| < TWO_TO_THE_32

    static const Empty: View :=
      View([], 0, 0)

    const Empty? :=
      beg == end

    function Length(): uint32 requires Valid? {
      end - beg
    }

    function Bytes(): bytes requires Valid? {
      s[beg..end]
    }

    static function OfBytes(bs: bytes) : (v: View)
      requires |bs| < TWO_TO_THE_32
      ensures v.Bytes() == bs
    {
      View(bs, 0 as uint32, |bs| as uint32)
    }

    static function OfString(s: string) : bytes
      requires forall c: char | c in s :: c as int < 256
    {
      seq(|s|, i requires 0 <= i < |s| =>
        assert s[i] in s; s[i] as byte)
    }

    ghost predicate SliceOf?(v': View) {
      v'.s == s && v'.beg <= beg && end <= v'.end
    }

    ghost predicate StrictPrefixOf?(v': View) {
      v'.s == s && v'.beg == beg && end < v'.end
    }

    ghost predicate StrictSuffixOf?(v': View) {
      v'.s == s && v'.beg < beg && end == v'.end
    }

    predicate Byte?(c: byte)
      requires Valid?
    {
      Bytes() == [c]
    } by method {
      return Length() == 1 && At(0) == c;
    }

    predicate Char?(c: char)
      requires Valid?
      requires c as int < 256
    {
      Byte?(c as byte)
    }

    ghost predicate ValidIndex?(idx: uint32) {
      beg as int + idx as int < end as int
    }

    function At(idx: uint32) : byte
      requires Valid?
      requires ValidIndex?(idx)
    {
      s[beg + idx]
    }

    function Peek(): (r: opt_byte)
      requires Valid?
      ensures r < 0 <==> Empty?
    {
      if Empty? then -1
      else At(0) as opt_byte
    }

    method CopyTo(dest: array<byte>, start: uint32 := 0)
      requires Valid?
      requires start as int + Length() as int <= dest.Length
      requires start as int + Length() as int < TWO_TO_THE_32
      modifies dest
      ensures dest[start..start + Length()] == Bytes()
      ensures dest[start + Length()..] == old(dest[start + Length()..])
    {
      for idx := 0 to Length()
        invariant dest[start..start + idx] == Bytes()[..idx]
        invariant dest[start + Length()..] == old(dest[start + Length()..])
      {
        dest[start + idx] := s[beg + idx];
      }
    }
  }

  predicate Adjacent(lv: View, rv: View) {
    // Compare endpoints first to short-circuit the potentially-costly string
    // comparison
    && lv.end == rv.beg
    // We would prefer to use reference equality here, but doing so in a sound
    // way is tricky (see chapter 9 of ‘Verasco: a Formally Verified C Static
    // Analyzer’ by Jacques-Henri Jourdan for details).  The runtime optimizes
    // the common case of physical equality and otherwise performs a length
    // check, so the worst case (checking for adjacency in two slices that have
    // equal but not physically-equal contents) is hopefully not too common.
    && lv.s == rv.s
  }

  function Merge(lv: View, rv: View) : (v: View)
    requires Adjacent(lv, rv)
    ensures v.Bytes() == lv.Bytes() + rv.Bytes()
  {
    lv.(end := rv.end)
  }
}
