/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/** An encoder and decoder for the Base64 encoding scheme. */
module Std.Base64 {
  import opened Wrappers
  import opened BoundedInts

  export
    reveals
      // Functions mentioned in contracts of functions provided below
      IsBase64Char,
      index,
      CharToIndex,
      IndexToChar,
      IsBase64String,
      IsUnpaddedBase64String,
      Is1Padding,
      Is2Padding
    provides
      // uint8-based API
      Encode,
      Decode,
      // bv8-based API
      EncodeBV,
      DecodeBV,
      // Lemmas
      EncodeDecode,
      DecodeEncode,
      EncodeDecodeBV,
      DecodeEncodeBV,
      // Dependencies
      BoundedInts,
      Wrappers

  export Internals
    reveals *

  // The maximum index for Base64 is less than 64 (0x40)
  type index = bv6

  predicate IsBase64Char(c: char) {
    // char values can be compared using standard relational operators
    // http://leino.science/papers/krml243.html#sec-char
    c == '+' || c == '/' || '0' <= c <= '9' || 'A' <= c <= 'Z' || 'a' <= c <= 'z'
  }

  lemma Base64CharIs7Bit(c: char)
    requires IsBase64Char(c)
    ensures c < 128 as char
  {
  }

  predicate IsUnpaddedBase64String(s: string) {
    // A Base64 encoded string will use 4 ASCII characters for every 3 bytes of data ==> length is divisible by 4
    |s| % 4 == 0 && forall k :: k in s ==> IsBase64Char(k)
  }

  function IndexToChar(i: index): (c: char)
    ensures IsBase64Char(c)
  {
    // Based on the Base64 index table
    if i == 63 then '/'
    else if i == 62 then '+'
    // Dafny 1.9.9 added support for char to int conversion
    // https://github.com/dafny-lang/dafny/releases/tag/v1.9.9
    // 0 - 9
    else if 52 <= i <= 61 then (i - 4) as int as char
    // a - z
    else if 26 <= i <= 51 then i as int as char + 71 as char
    // A - Z
    else i as int as char + 65 as char
  }

  lemma IndexToCharIsBase64(i: index)
    ensures IsBase64Char(IndexToChar(i))
  {
  }

  function CharToIndex(c: char): (i: index)
    // This is actually required for the function to be total,
    // and that requirement propagates to many places.
    requires IsBase64Char(c)
  {
    // Perform the inverse operations of IndexToChar
    if c == '/' then 63
    else if c == '+' then 62
    else if '0' <= c <= '9' then (c + 4 as char) as int as index
    else if 'a' <= c <= 'z' then (c - 71 as char) as int as index
    else (c - 65 as char) as int as index
  }

  @ResourceLimit("2e6")
  @IsolateAssertions
  lemma CharToIndexToChar(c: char)
    requires IsBase64Char(c)
    ensures IndexToChar(CharToIndex(c)) == c
  {
    // TODO: reduce resource use, brittleness
    Base64CharIs7Bit(c);
    if c == '/' {
      assert IndexToChar(CharToIndex(c)) == c;
    } else if c == '+' {
      assert IndexToChar(CharToIndex(c)) == c;
    } else if '0' <= c <= '9' {
      assert IndexToChar(CharToIndex(c)) == c;
    } else if 'a' <= c < 'm' {
      assert IndexToChar(CharToIndex(c)) == c;
    } else if 'm' <= c <= 'z' {
      assert IndexToChar(CharToIndex(c)) == c;
    } else {
      assert IndexToChar(CharToIndex(c)) == c;
    }
  }

  @IsolateAssertions
  lemma IndexToCharToIndex(i: index)
    ensures (IndexToCharIsBase64(i); CharToIndex(IndexToChar(i)) == i)
  {
    // TODO: reduce resource use, brittleness
    IndexToCharIsBase64(i);
    if i == 63 {
      assert CharToIndex(IndexToChar(i)) == i;
    } else if i == 62 {
      assert CharToIndex(IndexToChar(i)) == i;
    } else if 52 <= i <= 61 {
      assert CharToIndex(IndexToChar(i)) == i;
    } else if 26 <= i <= 51 {
      assert CharToIndex(IndexToChar(i)) == i;
    } else {
      assert CharToIndex(IndexToChar(i)) == i;
    }
  }

  lemma IndexToCharToIndexAuto()
    ensures forall x :: (IndexToCharIsBase64(x); CharToIndex(IndexToChar(x)) == x)
  {
    forall x: index
      ensures (IndexToCharIsBase64(x); CharToIndex(IndexToChar(x)) == x)
    {
      IndexToCharToIndex(x);
    }
  }

  lemma CharToIndexToCharAuto()
    ensures forall c | IsBase64Char(c) :: IndexToChar(CharToIndex(c)) == c
  {
    forall c: char | IsBase64Char(c)
      ensures IndexToChar(CharToIndex(c)) == c
    {
      CharToIndexToChar(c);
    }
  }

  function BV24ToSeq(x: bv24): (ret: seq<bv8>)
    ensures |ret| == 3
  {
    var b0 := ((x >> 16) & 0x0000FF) as bv8;
    var b1 := ((x >>  8) & 0x0000FF) as bv8;
    var b2 := ((x      ) & 0x0000FF) as bv8;
    [b0, b1, b2]
  }

  function SeqToBV24(x: seq<bv8>): (ret: bv24)
    requires |x| == 3
  {
    (x[0] as bv24 << 16) | (x[1] as bv24 << 8) | x[2] as bv24
  }

  lemma BV24ToSeqToBV24(x: bv24)
    ensures SeqToBV24(BV24ToSeq(x)) == x
  {
  }

  lemma SeqToBV24ToSeq(s: seq<bv8>)
    requires |s| == 3
    ensures BV24ToSeq(SeqToBV24(s)) == s
  {
  }

  function BV24ToIndexSeq(x: bv24): (ret: seq<index>)
    ensures |ret| == 4
  {
    var b0 := ((x >> 18) & 0x00003F) as index;
    var b1 := ((x >> 12) & 0x00003F) as index;
    var b2 := ((x >>  6) & 0x00003F) as index;
    var b3 := ((x      ) & 0x00003F) as index;
    [b0, b1, b2, b3]
  }

  function IndexSeqToBV24(x: seq<index>): (ret: bv24)
    requires |x| == 4
  {
    (x[0] as bv24 << 18) |
    (x[1] as bv24 << 12) |
    (x[2] as bv24 <<  6) |
    (x[3] as bv24      )
  }

  lemma BV24ToIndexSeqToBV24(x: bv24)
    ensures IndexSeqToBV24(BV24ToIndexSeq(x)) == x
  {
  }

  lemma IndexSeqToBV24ToIndexSeq(s: seq<index>)
    requires |s| == 4
    ensures BV24ToIndexSeq(IndexSeqToBV24(s)) == s
  {
  }

  function DecodeBlock(s: seq<index>): (ret: seq<bv8>)
    requires |s| == 4
    ensures |ret| == 3
  {
    BV24ToSeq(IndexSeqToBV24(s))
  }

  function EncodeBlock(s: seq<bv8>): (ret: seq<index>)
    requires |s| == 3
    ensures |ret| == 4
  {
    BV24ToIndexSeq(SeqToBV24(s))
  }

  lemma EncodeDecodeBlock(s: seq<bv8>)
    requires |s| == 3
    ensures DecodeBlock(EncodeBlock(s)) == s
  {
    var b := SeqToBV24(s);
    BV24ToIndexSeqToBV24(b);
    SeqToBV24ToSeq(s);
  }

  lemma DecodeEncodeBlock(s: seq<index>)
    requires |s| == 4
    ensures EncodeBlock(DecodeBlock(s)) == s
  {
    var b := IndexSeqToBV24(s);
    BV24ToSeqToBV24(b);
    IndexSeqToBV24ToIndexSeq(s);
  }

  @IsolateAssertions
  function DecodeRecursively(s: seq<index>): (b: seq<bv8>)
    requires |s| % 4 == 0
    decreases |s|
  {
    if |s| == 0 then []
    else DecodeBlock(s[..4]) + DecodeRecursively(s[4..])
  } by method {
    var resultLength := |s|/4 * 3;
    var result := new bv8[resultLength](i => 0);
    var i := |s|;
    var j := resultLength;

    while i > 0
      invariant i % 4 == 0
      invariant 0 <= i <= |s|
      invariant i * 3 == j * 4
      invariant 0 <= j <= resultLength
      invariant result[j..] == DecodeRecursively(s[i..])
    {
      i := i - 4;
      j := j - 3;
      var block := DecodeBlock(s[i..i+4]);
      result[j] := block[0];
      result[j+1] := block[1];
      result[j+2] := block[2];
      //assert result[j+3..] == DecodeRecursively(s[i+4..]);
      assert s[i..][..4] == s[i..i+4];
      assert s[i..][4..] == s[i+4..];
      assert result[j..j+3] == block;

      calc {
        DecodeBlock(s[i..i+4]) + DecodeRecursively(s[i+4..]);
        DecodeBlock(s[i..][..4]) + DecodeRecursively(s[i..][4..]);
        DecodeRecursively(s[i..]);
      }
    }
    b := result[..];
  }

  lemma DecodeRecursivelyBounds(s: seq<index>)
    requires |s| % 4 == 0
    ensures |DecodeRecursively(s)| == |s| / 4 * 3
    ensures |DecodeRecursively(s)| % 3 == 0
    ensures |DecodeRecursively(s)| == 0 ==> |s| == 0
  {
  }

  lemma DecodeRecursivelyBlock(s: seq<index>)
    requires |s| % 4 == 0
    ensures
      (DecodeRecursivelyBounds(s);
       var b := DecodeRecursively(s);
       |b| != 0 ==> EncodeBlock(b[..3]) == s[..4])
  {
    DecodeRecursivelyBounds(s);
    if |s| == 0 {}
    else {
      DecodeEncodeBlock(s[..4]);
    }
  }

  @IsolateAssertions
  function EncodeRecursively(b: seq<bv8>): (s: seq<index>)
    requires |b| % 3 == 0
  {
    if |b| == 0 then []
    else EncodeBlock(b[..3]) + EncodeRecursively(b[3..])
  } by method {
    var resultLength := |b|/3 * 4;
    var result := new index[resultLength](i => 0);
    var i := |b|;
    var j := resultLength;

    while i > 0
      invariant i % 3 == 0
      invariant 0 <= i <= |b|
      invariant i * 4 == j * 3
      invariant 0 <= j <= resultLength
      invariant result[j..] == EncodeRecursively(b[i..])
    {
      i := i - 3;
      j := j - 4;
      var block := EncodeBlock(b[i..i+3]);
      result[j] := block[0];
      result[j+1] := block[1];
      result[j+2] := block[2];
      result[j+3] := block[3];
      assert b[i..][..3] == b[i..i+3];
      assert b[i..][3..] == b[i+3..];
      assert result[j..j+4] == block;
      calc {
        EncodeBlock(b[i..i+3]) + EncodeRecursively(b[i+3..]);
        EncodeBlock(b[i..][..3]) + EncodeRecursively(b[i..][3..]);
        EncodeRecursively(b[i..]);
      }
    }
    s := result[..];
  }

  lemma EncodeRecursivelyBounds(b: seq<bv8>)
    requires |b| % 3 == 0
    ensures |EncodeRecursively(b)| == |b| / 3 * 4
    ensures |EncodeRecursively(b)| % 4 == 0
    ensures |EncodeRecursively(b)| == 0 ==> |b| == 0
  {
  }

  lemma EncodeRecursivelyBlock(b: seq<bv8>)
    requires |b| % 3 == 0
    ensures (EncodeRecursivelyBounds(b);
             var s := EncodeRecursively(b);
             |s| != 0 ==> DecodeBlock(s[..4]) == b[..3])
  {
    EncodeRecursivelyBounds(b);
    if |b| == 0 {}
    else {
      EncodeDecodeBlock(b[..3]);
    }
  }

  lemma {:isolate_assertions} EncodeDecodeRecursively(b: seq<bv8>)
    requires |b| % 3 == 0
    ensures (EncodeRecursivelyBounds(b); DecodeRecursively(EncodeRecursively(b)) == b)
  {
    hide *;

    var s := EncodeRecursively(b);
    EncodeRecursivelyBounds(b);
    DecodeRecursivelyBounds(s);

    if |b| == 0 {
    } else {
      calc {
        DecodeRecursively(EncodeRecursively(b));
      ==
        DecodeRecursively(s);
      == {
           assert |s[4..]| % 4 == 0;
           reveal DecodeRecursively;
         }
        DecodeBlock(s[..4]) + DecodeRecursively(s[4..]);
      == { EncodeRecursivelyBlock(b); }
        b[..3] + DecodeRecursively(s[4..]);
      == { reveal EncodeRecursively; }
        b[..3] + DecodeRecursively(EncodeRecursively(b[3..]));
      == { EncodeDecodeRecursively(b[3..]); }
        b[..3] + b[3..];
      ==
        b;
      }
    }
  }

  lemma {:isolate_assertions} DecodeEncodeRecursively(s: seq<index>)
    requires |s| % 4 == 0
    ensures (DecodeRecursivelyBounds(s); EncodeRecursively(DecodeRecursively(s)) == s)
  {
    hide *;
    var b := DecodeRecursively(s);
    DecodeRecursivelyBounds(s);
    EncodeRecursivelyBounds(b);
    if |s| == 0 {
    } else {
      calc {
        EncodeRecursively(DecodeRecursively(s));
      ==
        EncodeRecursively(b);
      == { reveal EncodeRecursively; }
        EncodeBlock(b[..3]) + EncodeRecursively(b[3..]);
      == { DecodeRecursivelyBlock(s); }
        s[..4] + EncodeRecursively(b[3..]);
      == { reveal DecodeRecursively; }
        s[..4] + EncodeRecursively(DecodeRecursively(s[4..]));
      == { DecodeEncodeRecursively(s[4..]); }
        s[..4] + s[4..];
      ==
        s;
      }
    }
  }

  function FromCharsToIndices(s: seq<char>): (b: seq<index>)
    requires forall k :: k in s ==> IsBase64Char(k)
    ensures |b| == |s|
  {
    seq(|s|, i requires 0 <= i < |s| => CharToIndex(s[i]))
  }

  function FromIndicesToChars(b: seq<index>): (s: seq<char>)
    ensures forall k :: k in s ==> IsBase64Char(k)
    ensures |s| == |b|
  {
    seq(|b|, i requires 0 <= i < |b| => IndexToChar(b[i]))
  }

  lemma FromCharsToIndicesToChars(s: seq<char>)
    requires forall k :: k in s ==> IsBase64Char(k)
    ensures FromIndicesToChars(FromCharsToIndices(s)) == s
  {
    CharToIndexToCharAuto();
  }

  lemma FromIndicesToCharsToIndices(b: seq<index>)
    ensures FromCharsToIndices(FromIndicesToChars(b)) == b
  {
    IndexToCharToIndexAuto();
  }

  function DecodeUnpadded(s: seq<char>): (b: seq<bv8>)
    requires IsUnpaddedBase64String(s)
  {
    DecodeRecursively(FromCharsToIndices(s))
  }

  lemma DecodeUnpaddedBounds(s: seq<char>)
    requires IsUnpaddedBase64String(s)
    ensures |DecodeUnpadded(s)| == |s| / 4 * 3
    ensures |DecodeUnpadded(s)| % 3 == 0
  {
    var indices := FromCharsToIndices(s);
    assert |indices| == |s|;
    DecodeRecursivelyBounds(indices);
  }

  function EncodeUnpadded(b: seq<bv8>): (s: seq<char>)
    requires |b| % 3 == 0
  {
    EncodeDecodeRecursively(b);
    FromIndicesToChars(EncodeRecursively(b))
  }

  lemma EncodeUnpaddedNotPadded(b: seq<bv8>)
    requires |b| % 3 == 0
    requires b != []
    ensures (EncodeUnpaddedBounds(b);
             var s := EncodeUnpadded(b);
             !Is1Padding(s[(|s| - 4)..]) && !Is2Padding(s[(|s| - 4)..]))
  {
    var s := EncodeUnpadded(b);
    EncodeUnpaddedBounds(b);
    var suffix := s[(|s| - 4)..];
    assert forall c :: c in s ==> IsBase64Char(c);
    assert IsBase64Char(s[|s| - 1]);
    assert s[|s| - 1] != '=';
  }

  lemma EncodeUnpaddedBounds(b: seq<bv8>)
    requires |b| % 3 == 0
    ensures |EncodeUnpadded(b)| == |b| / 3 * 4
    ensures |EncodeUnpadded(b)| % 4 == 0
  {
    EncodeRecursivelyBounds(b);
  }

  lemma EncodeUnpaddedBase64(b: seq<bv8>)
    requires |b| % 3 == 0
    ensures IsUnpaddedBase64String(EncodeUnpadded(b))
  {
    EncodeRecursivelyBounds(b);
  }

  lemma EncodeDecodeUnpadded(b: seq<bv8>)
    requires |b| % 3 == 0
    ensures (EncodeUnpaddedBounds(b); EncodeUnpaddedBase64(b); DecodeUnpadded(EncodeUnpadded(b)) == b)
  {
    EncodeUnpaddedBase64(b);
    calc {
      DecodeUnpadded(EncodeUnpadded(b));
    ==
      DecodeUnpadded(FromIndicesToChars(EncodeRecursively(b)));
    == {  EncodeRecursivelyBounds(b); }
      DecodeRecursively(FromCharsToIndices(FromIndicesToChars(EncodeRecursively(b))));
    == { FromIndicesToCharsToIndices(EncodeRecursively(b)); }
      DecodeRecursively(EncodeRecursively(b));
    == { EncodeDecodeRecursively(b); }
      b;
    }
  }

  lemma DecodeEncodeUnpadded(s: seq<char>)
    requires |s| % 4 == 0
    requires IsUnpaddedBase64String(s)
    ensures (DecodeUnpaddedBounds(s); EncodeUnpadded(DecodeUnpadded(s)) == s)
  {
    DecodeUnpaddedBounds(s);
    var fromCharsToIndicesS := FromCharsToIndices(s);
    calc {
      EncodeUnpadded(DecodeUnpadded(s));
    ==
      EncodeUnpadded(DecodeRecursively(FromCharsToIndices(s)));
    ==
      EncodeUnpadded(DecodeRecursively(fromCharsToIndicesS));
    ==
      assert |fromCharsToIndicesS| % 4 == 0;
      FromIndicesToChars(EncodeRecursively(DecodeRecursively(fromCharsToIndicesS)));
    == { DecodeEncodeRecursively(fromCharsToIndicesS); }
      FromIndicesToChars(fromCharsToIndicesS);
    ==
      FromIndicesToChars(FromCharsToIndices(s));
    == { FromCharsToIndicesToChars(s); }
      s;
    }
  }

  predicate Is1Padding(s: seq<char>) {
    |s| == 4 &&
    IsBase64Char(s[0]) &&
    IsBase64Char(s[1]) &&
    IsBase64Char(s[2]) &&
    // This is a result of the padded 0's in the sextet in the final element before the =
    CharToIndex(s[2]) & 0x3 == 0 && // Using & instead of % here makes the BV proofs easier
    s[3] == '='
  }

  function Decode1Padding(s: seq<char>): (b: seq<bv8>)
    requires Is1Padding(s)
    // Padding with 1 = implies the sequence represents 2 bytes
    ensures |b| == 2
  {
    var d := DecodeBlock([CharToIndex(s[0]), CharToIndex(s[1]), CharToIndex(s[2]), 0]);
    [d[0], d[1]]
  }

  function Encode1Padding(b: seq<bv8>): (s: seq<char>)
    requires |b| == 2
    ensures |s| % 4 == 0
    ensures |s| == 4
  {
    // 0 is used to ensure that the final element doesn't affect the EncodeBlock conversion for b
    var e := EncodeBlock([b[0], b[1], 0]);
    IndexToCharIsBase64(e[0]);
    IndexToCharIsBase64(e[1]);
    IndexToCharIsBase64(e[2]);
    [IndexToChar(e[0]), IndexToChar(e[1]), IndexToChar(e[2]), '=']
  }

  lemma EncodeDecodeBlock1Padding(b: seq<bv8>)
    requires |b| == 2
    ensures
      var e := EncodeBlock([b[0], b[1], 0]);
      var d := DecodeBlock([e[0], e[1], e[2], 0]);
      [d[0], d[1]] == b
  {
  }

  lemma {:resource_limit 0} Encode1PaddingIs1Padding(b: seq<bv8>)
    requires |b| == 2
    ensures Is1Padding(Encode1Padding(b))
  {
    hide *;

    var s := Encode1Padding(b);
    var e := EncodeBlock([b[0], b[1], 0]);

    reveal Encode1Padding; // TODO make by penetrate
    assert s == [IndexToChar(e[0]), IndexToChar(e[1]), IndexToChar(e[2]), '='] by {
    }
    IndexToCharIsBase64(e[0]);
    IndexToCharIsBase64(e[1]);
    IndexToCharIsBase64(e[2]);

    // TODO make by penetrate
    // TODO provide a way to reveal deeply.
    reveal Encode1Padding, EncodeBlock, IndexToChar, CharToIndex, BV24ToIndexSeq, SeqToBV24;
    assert CharToIndex(s[2]) & 0x3 == 0 by {
    }

    assert Is1Padding(s) by {
      reveal Is1Padding;
    }
  }

  lemma EncodeDecode1Padding(b: seq<bv8>)
    requires |b| == 2
    ensures (Encode1PaddingIs1Padding(b); Decode1Padding(Encode1Padding(b)) == b)
  {
    Encode1PaddingIs1Padding(b);
    var e := EncodeBlock([b[0], b[1], 0]);
    var s := [CharToIndex(IndexToChar(e[0])), CharToIndex(IndexToChar(e[1])), CharToIndex(IndexToChar(e[2])), 0];
    var s' := [e[0], e[1], e[2], 0];
    var d := DecodeBlock(s);
    var d' := DecodeBlock(s');
    calc {
      Decode1Padding(Encode1Padding(b));
    ==
      Decode1Padding([IndexToChar(e[0]), IndexToChar(e[1]), IndexToChar(e[2]), '=']);
    ==
      [d[0], d[1]];
    == { IndexToCharToIndex(e[0]); IndexToCharToIndex(e[1]); IndexToCharToIndex(e[2]); }
      [d'[0], d'[1]];
    == { EncodeDecodeBlock1Padding(b); }
      b;
    }
  }

  @IsolateAssertions
  lemma DecodeEncode1Padding(s: seq<char>)
    requires Is1Padding(s)
    ensures Encode1Padding(Decode1Padding(s)) == s
  {
    var i := [CharToIndex(s[0]), CharToIndex(s[1]), CharToIndex(s[2]), 0];
    var d := DecodeBlock(i);
    var e := EncodeBlock([d[0], d[1], 0]);
    var d' := [IndexToChar(e[0]), IndexToChar(e[1]), IndexToChar(e[2]), '='];
    calc {
      Encode1Padding(Decode1Padding(s));
    ==
      Encode1Padding([d[0], d[1]]);
    ==
      d';
    == {
         // This argument is easiest to make by just automating it
         // However, the mix between % and & in padding constraints
         // makes it a little difficult
         assert d'[0] == IndexToChar(CharToIndex(s[0]));
         assert d'[1] == IndexToChar(CharToIndex(s[1]));
         assert d'[2] == IndexToChar(CharToIndex(s[2]));
       }
      [IndexToChar(CharToIndex(s[0])), IndexToChar(CharToIndex(s[1])), IndexToChar(CharToIndex(s[2])), '='];
    == { CharToIndexToChar(s[0]); CharToIndexToChar(s[1]); CharToIndexToChar(s[2]); }
      s;
    }
  }

  predicate Is2Padding(s: seq<char>) {
    |s| == 4 &&
    IsBase64Char(s[0]) &&
    IsBase64Char(s[1]) &&
    // This is a result of the padded 0's in the sextet in the final element before the two =
    CharToIndex(s[1]) % 0x10 == 0 &&
    s[2] == '=' &&
    s[3] == '='
  }

  function Decode2Padding(s: seq<char>): (b: seq<bv8>)
    requires Is2Padding(s)
    // Padding with 2 = implies the sequence represents 1 byte
    ensures |b| == 1
  {
    var d := DecodeBlock([CharToIndex(s[0]), CharToIndex(s[1]), 0, 0]);
    [d[0]]
  }

  function Encode2Padding(b: seq<bv8>): (s: seq<char>)
    // Padding with 2 = implies the sequence represents 1 bytes
    requires |b| == 1
    ensures |s| % 4 == 0
    ensures |s| == 4
  {
    // 0 is used to ensure that the final two elements don't affect the EncodeBlock conversion for b
    var e := EncodeBlock([b[0], 0, 0]);
    IndexToCharIsBase64(e[0]);
    IndexToCharIsBase64(e[1]);
    [IndexToChar(e[0]), IndexToChar(e[1]), '=', '=']
  }

  lemma Encode2PaddingIs2Padding(b: seq<bv8>)
    requires |b| == 1
    ensures Is2Padding(Encode2Padding(b))
  {
  }

  lemma DecodeEncodeBlock2Padding(b: seq<bv8>)
    requires |b| == 1
    ensures
      var e := EncodeBlock([b[0], 0, 0]);
      var d := DecodeBlock([e[0], e[1], 0, 0]);
      [d[0]] == b
  {
  }

  lemma EncodeDecode2Padding(b: seq<bv8>)
    requires |b| == 1
    ensures (Encode2PaddingIs2Padding(b); Decode2Padding(Encode2Padding(b)) == b)
  {
    Encode2PaddingIs2Padding(b);
    var e := EncodeBlock([b[0], 0, 0]);
    calc {
      Decode2Padding(Encode2Padding(b));
    ==
      Decode2Padding([IndexToChar(e[0]), IndexToChar(e[1]), '=', '=']);
    ==
      [DecodeBlock([CharToIndex(IndexToChar(e[0])), CharToIndex(IndexToChar(e[1])), 0, 0])[0]];
    == { IndexToCharToIndex(e[0]); IndexToCharToIndex(e[1]); }
      [DecodeBlock([e[0], e[1], 0, 0])[0]];
    == { DecodeEncodeBlock2Padding(b); }
      b;
    }
  }

  lemma DecodeEncode2Padding(s: seq<char>)
    requires Is2Padding(s)
    ensures Encode2Padding(Decode2Padding(s)) == s
  {
    var i := [CharToIndex(s[0]), CharToIndex(s[1]), 0, 0];
    var d := DecodeBlock(i);
    var e := EncodeBlock([d[0], 0, 0]);
    var d' := [IndexToChar(e[0]), IndexToChar(e[1]), '=', '='];
    calc {
      Encode2Padding(Decode2Padding(s));
    ==
      Encode2Padding([d[0]]);
    ==
      d';
    == {
         // This argument is easiest to make by just automating it
       }
      [IndexToChar(CharToIndex(s[0])), IndexToChar(CharToIndex(s[1])), '=', '='];
    == { CharToIndexToChar(s[0]); CharToIndexToChar(s[1]); }
      s;
    }
  }

  predicate IsBase64String(s: string) {
    // All Base64 strings are unpadded until the final block of 4 elements, where a padded seq could exist
    var finalBlockStart := |s| - 4;
    (|s| % 4 == 0) &&
    (IsUnpaddedBase64String(s) ||
     (IsUnpaddedBase64String(s[..finalBlockStart]) && (Is1Padding(s[finalBlockStart..]) || Is2Padding(s[finalBlockStart..]))))
  }

  function DecodeValid(s: seq<char>): (b: seq<bv8>)
    requires IsBase64String(s)
  {
    if s == [] then [] else
    var finalBlockStart := |s| - 4;
    var prefix, suffix := s[..finalBlockStart], s[finalBlockStart..];
    if Is1Padding(suffix) then
      DecodeUnpadded(prefix) + Decode1Padding(suffix)
    else if Is2Padding(suffix) then
      DecodeUnpadded(prefix) + Decode2Padding(suffix)
    else
      DecodeUnpadded(s)
  }

  lemma AboutDecodeValid(s: seq<char>, b: seq<bv8>)
    requires IsBase64String(s) && b == DecodeValid(s)
    ensures 4 <= |s| ==> var finalBlockStart := |s| - 4;
                         var prefix, suffix := s[..finalBlockStart], s[finalBlockStart..];
                         && (Is1Padding(suffix) && IsUnpaddedBase64String(prefix) <==> (|b| % 3 == 2 && |b| > 1))
                         && (Is2Padding(suffix) && IsUnpaddedBase64String(prefix) <==> (|b| % 3 == 1 && |b| > 0))
                         && (!Is1Padding(suffix) && !Is2Padding(suffix) && IsUnpaddedBase64String(s) <==> (|b| % 3 == 0 && |b| > 1))
  {

    if 4 <= |s| {
      var finalBlockStart := |s| - 4;
      var prefix, suffix := s[..finalBlockStart], s[finalBlockStart..];

      if s == [] {
      } else if Is1Padding(suffix) {
        assert !Is2Padding(suffix) by {
        }
        var x, y := DecodeUnpadded(prefix), Decode1Padding(suffix);
        assert b == x + y;
        assert |x| == |x| / 3 * 3 && |y| == 2 && |b| > 1 by {
          DecodeUnpaddedBounds(prefix);
        }
        Mod3(|x| / 3, |y|, |b|);
      } else if Is2Padding(suffix) {
        var x, y := DecodeUnpadded(prefix), Decode2Padding(suffix);
        assert b == x + y;
        assert |x| == |x| / 3 * 3 && |y| == 1 && |b| > 0 by {
          DecodeUnpaddedBounds(prefix);
        }
        Mod3(|x| / 3, |y|, |b|);
      } else {
        assert b == DecodeUnpadded(s);
        assert |b| % 3 == 0 && |b| > 1 by {
          DecodeUnpaddedBounds(s);
        }
      }
    }
  }

  lemma Mod3(x: nat, k: nat, n: nat)
    requires k < 3 && n == 3 * x + k
    ensures n % 3 == k
  {
  }

  function DecodeBV(s: seq<char>): (b: Result<seq<bv8>, string>)
    ensures IsBase64String(s) ==> b.Success? // Hard to use without this
  {
    if IsBase64String(s) then Success(DecodeValid(s)) else Failure("The encoding is malformed")
  }

  lemma DecodeBVFailure(s: seq<char>)
    ensures !IsBase64String(s) ==> DecodeBV(s).Failure?
  {
  }

  ghost predicate StringIs7Bit(s: string) {
    forall c :: c in s ==> c < 128 as char
  }

  lemma UnpaddedBase64StringIs7Bit(s: string)
    requires IsUnpaddedBase64String(s)
    ensures StringIs7Bit(s)
  {
  }

  lemma Is7Bit1Padding(s: string)
    requires Is1Padding(s)
    ensures StringIs7Bit(s)
  {
  }

  lemma Is7Bit2Padding(s: string)
    requires Is2Padding(s)
    ensures StringIs7Bit(s)
  {
  }

  function EncodeBV(b: seq<bv8>): (s: seq<char>)
    // Rather than ensure Decode(s) == Success(b) directly, lemmas are used to verify this property
  {
    if |b| % 3 == 0 then
      EncodeUnpaddedBounds(b);
      EncodeUnpadded(b)
    else if |b| % 3 == 1 then
      assert |b| >= 1;
      EncodeUnpaddedBounds(b[..(|b| - 1)]);
      var s1, s2 := EncodeUnpadded(b[..(|b| - 1)]), Encode2Padding(b[(|b| - 1)..]);
      s1 + s2
    else
      assert |b| % 3 == 2;
      assert |b| >= 2;
      EncodeUnpaddedBounds(b[..(|b| - 2)]);
      var s1, s2 := EncodeUnpadded(b[..(|b| - 2)]), Encode1Padding(b[(|b| - 2)..]);
      s1 + s2
  }

  lemma EncodeBVIsUnpadded(b: seq<bv8>)
    requires |b| % 3 == 0
    ensures EncodeBV(b) == EncodeUnpadded(b)
  {  }

  lemma EncodeBVIs2Padded(b: seq<bv8>)
    requires |b| % 3 == 1
    ensures EncodeBV(b) == EncodeUnpadded(b[..(|b| - 1)]) + Encode2Padding(b[(|b| - 1)..])
  {  }

  lemma EncodeBVIs1Padded(b: seq<bv8>)
    requires |b| % 3 == 2
    ensures EncodeBV(b) == EncodeUnpadded(b[..(|b| - 2)]) + Encode1Padding(b[(|b| - 2)..])
  {  }

  lemma EncodeBVLengthCongruentToZeroMod4(b: seq<bv8>)
    ensures |EncodeBV(b)| % 4 == 0
  {
    if |b| % 3 == 0 {
      EncodeUnpaddedBounds(b);
    } else if |b| % 3 == 1 {
      EncodeUnpaddedBounds(b[..(|b| - 1)]);
    } else {
      EncodeUnpaddedBounds(b[..(|b| - 2)]);
    }
  }

  lemma EncodeBVIsBase64(b: seq<bv8>)
    ensures IsBase64String(EncodeBV(b))
  {
    EncodeBVLengthExact(b);
    if |EncodeBV(b)| < 4 {
    } else if |b| % 3 == 0 {
      EncodeUnpaddedBase64(b);
    } else if |b| % 3 == 1 {
      var bStart := b[..(|b| - 1)];
      var bEnd := b[(|b| - 1)..];
      EncodeUnpaddedBase64(bStart);
      Encode2PaddingIs2Padding(bEnd);
    } else {
      var bStart := b[..(|b| - 2)];
      var bEnd := b[(|b| - 2)..];
      EncodeUnpaddedBase64(bStart);
      Encode1PaddingIs1Padding(bEnd);
    }
  }

  lemma EncodeBVLengthExact(b: seq<bv8>)
    ensures var s := EncodeBV(b);
            && (|b| % 3 == 0 ==> |s| == |b| / 3 * 4)
            && (|b| % 3 != 0 ==> |s| == |b| / 3 * 4 + 4)
  {

    var s := EncodeBV(b);
    if |b| % 3 == 0 {
      assert s == EncodeUnpadded(b);
      EncodeUnpaddedBounds(b);
      assert |s| == |b| / 3 * 4;
    } else if |b| % 3 == 1 {
      EncodeUnpaddedBounds(b[..(|b| - 1)]);
      assert s == EncodeUnpadded(b[..(|b| - 1)]) + Encode2Padding(b[(|b| - 1)..]);
      calc {
        |s|;
      ==
        |EncodeUnpadded(b[..(|b| - 1)])| + |Encode2Padding(b[(|b| - 1)..])|;
      ==  { assert |Encode2Padding(b[(|b| - 1)..])| == 4; }
        |EncodeUnpadded(b[..(|b| - 1)])| + 4;
      ==  { assert |EncodeUnpadded(b[..(|b| - 1)])| == |b[..(|b| - 1)]| / 3 * 4; }
        |b[..(|b| - 1)]| / 3 * 4 + 4;
      ==  { assert |b[..(|b| - 1)]| == |b| - 1; }
        (|b| - 1) / 3 * 4 + 4;
      ==  { assert (|b| - 1) / 3 == |b| / 3; }
        |b| / 3 * 4 + 4;
      }
    } else {
      EncodeUnpaddedBounds(b[..(|b| - 2)]);
      assert s == EncodeUnpadded(b[..(|b| - 2)]) + Encode1Padding(b[(|b| - 2)..]);
      Encode1PaddingIs1Padding(b[(|b| - 2)..]);
      calc {
        |s|;
      ==
        |EncodeUnpadded(b[..(|b| - 2)])| + |Encode1Padding(b[(|b| - 2)..])|;
      ==  { assert |Encode1Padding(b[(|b| - 2)..])| == 4; }
        |EncodeUnpadded(b[..(|b| - 2)])| + 4;
      ==  { assert |EncodeUnpadded(b[..(|b| - 2)])| == |b[..(|b| - 2)]| / 3 * 4; }
        |b[..(|b| - 2)]| / 3 * 4 + 4;
      ==  { assert |b[..(|b| - 2)]| == |b| - 2; }
        (|b| - 2) / 3 * 4 + 4;
      ==  { assert (|b| - 2) / 3 == |b| / 3; }
        |b| / 3 * 4 + 4;
      }
    }
  }

  lemma EncodeBVLengthBound(b: seq<bv8>)
    ensures var s := EncodeBV(b);
            |s| <= |b| / 3 * 4 + 4
  {
    EncodeBVLengthExact(b);
  }

  lemma SeqPartsMakeWhole<T>(s: seq<T>, i: nat)
    requires i <= |s|
    ensures s[..i] + s[i..] == s
  {}

  lemma DecodeValidEncodeEmpty(s: seq<char>)
    requires s == []
    ensures   EncodeBV(DecodeValid(s)) == s
  {
    assert IsBase64String(s) by {   }
    var b := DecodeValid(s);
    assert b == [];
    assert EncodeBV(b) == [] by {
    }
  }

  lemma EncodeDecodeValidEmpty(b: seq<bv8>)
    requires b == []
    ensures (EncodeBVIsBase64(b); DecodeValid(EncodeBV(b)) == b)
  {
    assert EncodeBV(b) == [] by {
    }
    EncodeBVIsBase64(b);
    assert DecodeValid([]) == [] by {
    }
  }

  lemma DecodeValidEncodeUnpadded(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires !Is1Padding(s[(|s| - 4)..])
    requires !Is2Padding(s[(|s| - 4)..])
    ensures EncodeBV(DecodeValid(s)) == s
  {
    DecodeUnpaddedBounds(s);
    calc {
      EncodeBV(DecodeValid(s));
    ==
      EncodeBV(DecodeUnpadded(s));
    ==
      EncodeUnpadded(DecodeUnpadded(s));
    == { DecodeEncodeUnpadded(s); }
      s;
    }
  }

  lemma EncodeDecodeValidUnpadded(b: seq<bv8>)
    requires |b| % 3 == 0
    requires b != []
    ensures
      var s := EncodeBV(b);
      && IsUnpaddedBase64String(s)
      && |s| >= 4
      && !Is1Padding(s[(|s| - 4)..])
      && !Is2Padding(s[(|s| - 4)..])
      && s == EncodeUnpadded(b)
  {
    EncodeUnpaddedBase64(b);
    EncodeUnpaddedBounds(b);
    var s := EncodeBV(b);
    assert s == EncodeUnpadded(b) by { EncodeBVIsUnpadded(b); }
    assert !Is1Padding(s[(|s| - 4)..]) by { EncodeUnpaddedNotPadded(b); }
    assert !Is2Padding(s[(|s| - 4)..]) by { EncodeUnpaddedNotPadded(b); }
  }

  lemma {:resource_limit "6e6"} EncodeDecodeValid2Padded(b: seq<bv8>)
    requires |b| % 3 == 1
    ensures
      var s := EncodeBV(b);
      && s == (EncodeUnpadded(b[..(|b| - 1)]) + Encode2Padding(b[(|b| - 1)..]))
      && Is2Padding(s[(|s| - 4)..])
  {
    hide *;
    reveal EncodeBV;

    EncodeUnpaddedBase64(b[..(|b| - 1)]);
    EncodeUnpaddedBounds(b[..(|b| - 1)]);
    var s := EncodeBV(b);
    Encode2PaddingIs2Padding(b[(|b| - 1)..]);
    assert Is2Padding(s[(|s| - 4)..]);
  }

  lemma EncodeDecodeValid1Padded(b: seq<bv8>)
    requires |b| % 3 == 2
    ensures
      var s := EncodeBV(b);
      && s == (EncodeUnpadded(b[..(|b| - 2)]) + Encode1Padding(b[(|b| - 2)..]))
      && |s| >= 4
      && IsUnpaddedBase64String(s[..(|s| - 4)])
      && Is1Padding(s[(|s| - 4)..])
  {
    EncodeUnpaddedBase64(b[..(|b| - 2)]);
    EncodeUnpaddedBounds(b[..(|b| - 2)]);
    var s := EncodeBV(b);
    Encode1PaddingIs1Padding(b[(|b| - 2)..]);
    assert Is1Padding(s[(|s| - 4)..]);
  }


  lemma DecodeValidUnpaddedPartialFrom1PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[(|s| - 4)..])
    ensures    DecodeValid(s)[..(|DecodeValid(s)| - 2)] == DecodeUnpadded(s[..(|s| - 4)])
  {
  }

  lemma DecodeValid1PaddedPartialFrom1PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[(|s| - 4)..])
    ensures  DecodeValid(s)[(|DecodeValid(s)| - 2)..] == Decode1Padding(s[(|s| - 4)..])
  {
  }

  lemma DecodeValid1PaddingLengthMod3(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[(|s| - 4)..])
    ensures |DecodeValid(s)| % 3 == 2
  {
    assert IsUnpaddedBase64String(s[..(|s| - 4)]) by {
      UnpaddedBase64Prefix(s);
    }
    AboutDecodeValid(s, DecodeValid(s));
  }

  @ResourceLimit("12e6")
  lemma DecodeValidEncode1Padding(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[(|s| - 4)..])
    ensures EncodeBV(DecodeValid(s)) == s
  {
    assert |DecodeValid(s)| % 3 == 2 by { DecodeValid1PaddingLengthMod3(s); }
    calc {
      EncodeBV(DecodeValid(s));
    ==
      EncodeUnpadded(DecodeValid(s)[..(|DecodeValid(s)| - 2)]) + Encode1Padding(DecodeValid(s)[(|DecodeValid(s)| - 2)..]);
    == { DecodeValidUnpaddedPartialFrom1PaddedSeq(s);   }
      EncodeUnpadded(DecodeUnpadded(s[..(|s| - 4)])) + Encode1Padding(DecodeValid(s)[(|DecodeValid(s)| - 2)..]);
    == {  DecodeEncodeUnpadded(s[..(|s| - 4)]); }
      s[..(|s| - 4)] + Encode1Padding(DecodeValid(s)[(|DecodeValid(s)| - 2)..]);
    == { DecodeValid1PaddedPartialFrom1PaddedSeq(s); }
      s[..(|s| - 4)] + Encode1Padding(Decode1Padding(s[(|s| - 4)..]));
    == { DecodeEncode1Padding(s[(|s| - 4)..]); }
      s[..(|s| - 4)] + s[(|s| - 4)..];
    == { SeqPartsMakeWhole(s, (|s| - 4)); }
      s;
    }
  }

  lemma DecodeValidPartialsFrom2PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is2Padding(s[(|s| - 4)..])
    ensures
      (
        var b := DecodeValid(s);
        b[..(|b| - 1)] == DecodeUnpadded(s[..(|s| - 4)]) &&
        b[(|b| - 1)..] == Decode2Padding(s[(|s| - 4)..]))
  {
    AboutDecodeValid(s, DecodeValid(s));
    assert Is2Padding(s[(|s| - 4)..]);
  }

  lemma DecodeValidPartialsFrom1PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[(|s| - 4)..])
    ensures
      (
        var b := DecodeValid(s);
        b[..(|b| - 2)] == DecodeUnpadded(s[..(|s| - 4)]) &&
        b[(|b| - 2)..] == Decode1Padding(s[(|s| - 4)..]))
  {
    AboutDecodeValid(s, DecodeValid(s));
  }

  lemma UnpaddedBase64Prefix(s: string)
    requires IsBase64String(s)
    requires |s| >= 4
    ensures IsUnpaddedBase64String(s[..(|s| - 4)])
  {
  }

  lemma DecodeValid2PaddingLengthMod3(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is2Padding(s[(|s| - 4)..])
    ensures |DecodeValid(s)| % 3 == 1
  {
    assert IsUnpaddedBase64String(s[..(|s| - 4)]) by {
      UnpaddedBase64Prefix(s);
    }
    AboutDecodeValid(s, DecodeValid(s));
  }

  lemma DecodeValidEncode2Padding(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is2Padding(s[(|s| - 4)..])
    ensures EncodeBV(DecodeValid(s)) == s
  {
    assert |DecodeValid(s)| % 3 == 1 by { DecodeValid2PaddingLengthMod3(s); }
    calc {
      EncodeBV(DecodeValid(s));
    ==
      EncodeUnpadded(DecodeValid(s)[..(|DecodeValid(s)| - 1)]) + Encode2Padding(DecodeValid(s)[(|DecodeValid(s)| - 1)..]);
    == { DecodeValidPartialsFrom2PaddedSeq(s);   }
      EncodeUnpadded(DecodeUnpadded(s[..(|s| - 4)])) + Encode2Padding(DecodeValid(s)[(|DecodeValid(s)| - 1)..]);
    == {  DecodeEncodeUnpadded(s[..(|s| - 4)]); }
      s[..(|s| - 4)] + Encode2Padding(DecodeValid(s)[(|DecodeValid(s)| - 1)..]);
    == { DecodeValidPartialsFrom2PaddedSeq(s); }
      s[..(|s| - 4)] + Encode2Padding(Decode2Padding(s[(|s| - 4)..]));
    == { DecodeEncode2Padding(s[(|s| - 4)..]); }
      s[..(|s| - 4)] + s[(|s| - 4)..];
    == { SeqPartsMakeWhole(s, (|s| - 4)); }
      s;
    }
  }

  lemma DecodeValidEncode(s: seq<char>)
    requires IsBase64String(s)
    ensures EncodeBV(DecodeValid(s)) == s
  {
    if s == [] {
      calc {
        EncodeBV(DecodeValid(s));
      == { DecodeValidEncodeEmpty(s); }
        s;
      }
    } else if |s| >= 4 && Is1Padding(s[(|s| - 4)..]) {
      calc {
        EncodeBV(DecodeValid(s));
      == { DecodeValidEncode1Padding(s); }
        s;
      }
    } else if |s| >= 4 && Is2Padding(s[(|s| - 4)..]) {
      calc {
        EncodeBV(DecodeValid(s));
      == { DecodeValidEncode2Padding(s); }
        s;
      }
    } else {
      calc {
        EncodeBV(DecodeValid(s));
      == { DecodeValidEncodeUnpadded(s); }
        s;
      }
    }
  }

  lemma EncodeDecodeValid(b: seq<bv8>)
    ensures (EncodeBVIsBase64(b); DecodeValid(EncodeBV(b)) == b)
  {
    hide *;
    EncodeBVIsBase64(b);
    var s := EncodeBV(b);
    if b == [] {
      calc {
        DecodeValid(EncodeBV(b));
      == { EncodeDecodeValidEmpty(b); }
        b;
      }
    } else if |b| % 3 == 0 {
      calc {
        DecodeValid(EncodeBV(b));
      == { EncodeBVIsUnpadded(b); }
        DecodeValid(EncodeUnpadded(b));
      == { reveal DecodeValid; EncodeDecodeValidUnpadded(b);  }
        DecodeUnpadded(EncodeUnpadded(b));
      == { EncodeDecodeUnpadded(b); }
        b;
      }
    } else if |b| % 3 == 1 {
      EncodeDecodeValid2Padded(b);
      var prefix := b[..(|b| - 1)];
      var suffix := b[(|b| - 1)..];
      EncodeUnpaddedBase64(prefix);

      calc {
        DecodeValid(EncodeBV(b));
      ==
        DecodeValid(EncodeUnpadded(prefix) + Encode2Padding(suffix));
      == {  DecodeValidPartialsFrom2PaddedSeq(s); }
        DecodeUnpadded(EncodeUnpadded(prefix)) + Decode2Padding(Encode2Padding(suffix));
      == { EncodeDecodeUnpadded(prefix); EncodeDecode2Padding(suffix); }
        prefix + suffix;
      ==
        b;
      }
    } else if |b| % 3 == 2 {
      EncodeDecodeValid1Padded(b);
      var prefix := b[..(|b| - 2)];
      var suffix := b[(|b| - 2)..];
      EncodeUnpaddedBase64(prefix);

      calc {
        DecodeValid(EncodeBV(b));
      ==
        DecodeValid(EncodeUnpadded(prefix) + Encode1Padding(suffix));
      == {  DecodeValidPartialsFrom1PaddedSeq(s); }
        DecodeUnpadded(EncodeUnpadded(prefix)) + Decode1Padding(Encode1Padding(suffix));
      == { EncodeDecodeUnpadded(prefix); EncodeDecode1Padding(suffix); }
        prefix + suffix;
      ==
        b;
      }
    }
  }

  lemma DecodeEncodeBV(s: seq<char>)
    requires IsBase64String(s)
    ensures EncodeBV(DecodeBV(s).value) == s
  {
    calc {
      EncodeBV(DecodeBV(s).value);
    == { DecodeValidEncode(s); }
      s;
    }
  }

  lemma EncodeDecodeBV(b: seq<bv8>)
    ensures DecodeBV(EncodeBV(b)) == Success(b)
  {
    EncodeBVIsBase64(b);
    calc {
      DecodeBV(EncodeBV(b));
    == { assert IsBase64String(EncodeBV(b)); }
      Success(DecodeValid(EncodeBV(b)));
    == { EncodeDecodeValid(b); }
      Success(b);
    }
  }

  function UInt8sToBVs(u: seq<uint8>): (r: seq<bv8>)
    ensures |r| == |u|
    ensures forall i :: 0 <= i < |u| ==> r[i] == u[i] as bv8
  {
    seq(|u|, i requires 0 <= i < |u| => u[i] as bv8)
  }

  function BVsToUInt8s(b: seq<bv8>): (r: seq<uint8>)
    ensures |r| == |b|
    ensures forall i :: 0 <= i < |b| ==> r[i] == b[i] as uint8
  {
    seq(|b|, i requires 0 <= i < |b| => b[i] as uint8)
  }

  @IsolateAssertions
  @ResourceLimit("1e9")
  lemma UInt8sToBVsToUInt8s(u: seq<uint8>)
    ensures BVsToUInt8s(UInt8sToBVs(u)) == u
  {
    // TODO: reduce resource use
    var b := UInt8sToBVs(u);
    assert |b| == |u|;
    var u' := BVsToUInt8s(b);
    assert |u'| == |b|;
  }

  lemma BVsToUInt8sToBVs(b: seq<bv8>)
    ensures UInt8sToBVs(BVsToUInt8s(b)) == b
  {
    var u := BVsToUInt8s(b);
    assert |b| == |u|;
    var b' := UInt8sToBVs(u);
    assert |b'| == |u|;
  }

  function Encode(u: seq<uint8>): seq<char> {
    EncodeBV(UInt8sToBVs(u))
  }

  function Decode(s: seq<char>): (b: Result<seq<uint8>, string>)
    ensures IsBase64String(s) ==> b.Success? // Hard to use without this
  {
    if IsBase64String(s)
    then
      var b := DecodeValid(s);
      Success(BVsToUInt8s(b))
    else Failure("The encoding is malformed")
  }

  lemma EncodeDecode(b: seq<uint8>)
    ensures Decode(Encode(b)) == Success(b)
  {
    var bvs := UInt8sToBVs(b);
    var s := EncodeBV(bvs);
    assert Encode(b) == s;
    assert IsBase64String(s) by { EncodeBVIsBase64(bvs); }
    var b' := DecodeValid(s);
    assert b' == bvs by { EncodeDecodeValid(bvs); }
    var us := BVsToUInt8s(b');
    assert Decode(s) == Success(us) by {
    }
    assert b' == bvs;
    assert b == us by { UInt8sToBVsToUInt8s(b); }
  }

  lemma DecodeEncode(s: seq<char>)
    requires IsBase64String(s)
    ensures Encode(Decode(s).value) == s
  {
    var b := DecodeValid(s);
    var u := BVsToUInt8s(b);
    assert Decode(s) == Success(u);
    var s' := EncodeBV(UInt8sToBVs(u));
    assert s' == Encode(u);
    assert UInt8sToBVs(BVsToUInt8s(b)) == b by {
      BVsToUInt8sToBVs(b);
    }
    assert s == s' by {
      DecodeValidEncode(s);
    }
  }
}
