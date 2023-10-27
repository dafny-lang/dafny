// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

/*
 * Note that additional lemmas for this module are in Base64Lemmas.dfy.
 */
module Base64 {
  import opened DafnyStdLibs.Wrappers
  import opened DafnyStdLibs.BoundedInts

  // The maximum index for Base64 is less than 64 (0x40)
  type index = bv6

  opaque predicate IsBase64Char(c: char) {
    // char values can be compared using standard relational operators
    // http://leino.science/papers/krml243.html#sec-char
    c == '+' || c == '/' || '0' <= c <= '9' || 'A' <= c <= 'Z' || 'a' <= c <= 'z'
  }

  lemma Base64CharIs7Bit(c: char)
    requires IsBase64Char(c)
    ensures c < 128 as char
  {
    reveal IsBase64Char();
  }

  opaque predicate IsUnpaddedBase64String(s: string) {
    // A Base64 encoded string will use 4 ASCII characters for every 3 bytes of data ==> length is divisible by 4
    |s| % 4 == 0 && forall k :: k in s ==> IsBase64Char(k)
  }

  opaque function IndexToChar(i: index): (c: char)
    ensures IsBase64Char(c)
  {
    reveal IsBase64Char();
    // Based on the Base64 index table
    if i == 63 then '/'
    else if i == 62 then '+'
    // Dafny 1.9.9 added support for char to int conversion
    // https://github.com/dafny-lang/dafny/releases/tag/v1.9.9
    // 0 - 9
    else if 52 <= i <= 61 then (i - 4) as char
    // a - z
    else if 26 <= i <= 51 then i as char + 71 as char
    // A - Z
    else i as char + 65 as char
  }

  lemma IndexToCharIsBase64(i: index)
    ensures IsBase64Char(IndexToChar(i))
  {
    reveal IndexToChar();
    reveal IsBase64Char();
  }

  opaque function CharToIndex(c: char): (i: index)
    // This is actually required for the function to be total,
    // and that requirement propagates to many places.
    requires IsBase64Char(c)
  {
    reveal IsBase64Char();
    reveal IndexToChar();
    // Perform the inverse operations of IndexToChar
    if c == '/' then 63
    else if c == '+' then 62
    else if '0' <= c <= '9' then (c + 4 as char) as index
    else if 'a' <= c <= 'z' then (c - 71 as char) as index
    else (c - 65 as char) as index
  }

  lemma {:vcs_split_on_every_assert} CharToIndexToChar(c: char)
    requires IsBase64Char(c)
    ensures IndexToChar(CharToIndex(c)) == c
  {
    // TODO: reduce resource use, brittleness
    Base64CharIs7Bit(c);
    reveal IsBase64Char();
    reveal IndexToChar();
    reveal CharToIndex();
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

  lemma {:vcs_split_on_every_assert} IndexToCharToIndex(i: index)
    ensures (IndexToCharIsBase64(i); CharToIndex(IndexToChar(i)) == i)
  {
    // TODO: reduce resource use, brittleness
    reveal IsBase64Char();
    reveal IndexToChar();
    reveal CharToIndex();
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

  opaque function BV24ToSeq(x: bv24): (ret: seq<bv8>)
    ensures |ret| == 3
  {
    var b0 := ((x >> 16) & 0x0000FF) as bv8;
    var b1 := ((x >>  8) & 0x0000FF) as bv8;
    var b2 := ((x      ) & 0x0000FF) as bv8;
    [b0, b1, b2]
  }

  opaque function SeqToBV24(x: seq<bv8>): (ret: bv24)
    requires |x| == 3
  {
    (x[0] as bv24 << 16) | (x[1] as bv24 << 8) | x[2] as bv24
  }

  lemma BV24ToSeqToBV24(x: bv24)
    ensures SeqToBV24(BV24ToSeq(x)) == x
  {
    reveal BV24ToSeq();
    reveal SeqToBV24();
  }

  lemma SeqToBV24ToSeq(s: seq<bv8>)
    requires |s| == 3
    ensures BV24ToSeq(SeqToBV24(s)) == s
  {
    reveal SeqToBV24();
    reveal BV24ToSeq();
  }

  opaque function BV24ToIndexSeq(x: bv24): (ret: seq<index>)
    ensures |ret| == 4
  {
    var b0 := ((x >> 18) & 0x00003F) as index;
    var b1 := ((x >> 12) & 0x00003F) as index;
    var b2 := ((x >>  6) & 0x00003F) as index;
    var b3 := ((x      ) & 0x00003F) as index;
    [b0, b1, b2, b3]
  }

  opaque function IndexSeqToBV24(x: seq<index>): (ret: bv24)
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
    reveal IndexSeqToBV24();
    reveal BV24ToIndexSeq();
  }

  lemma IndexSeqToBV24ToIndexSeq(s: seq<index>)
    requires |s| == 4
    ensures BV24ToIndexSeq(IndexSeqToBV24(s)) == s
  {
    reveal IndexSeqToBV24();
    reveal BV24ToIndexSeq();
  }

  opaque function DecodeBlock(s: seq<index>): (ret: seq<bv8>)
    requires |s| == 4
    ensures |ret| == 3
  {
    BV24ToSeq(IndexSeqToBV24(s))
  }

  opaque function EncodeBlock(s: seq<bv8>): (ret: seq<index>)
    requires |s| == 3
    ensures |ret| == 4
  {
    BV24ToIndexSeq(SeqToBV24(s))
  }

  lemma EncodeDecodeBlock(s: seq<bv8>)
    requires |s| == 3
    ensures DecodeBlock(EncodeBlock(s)) == s
  {
    reveal EncodeBlock();
    reveal DecodeBlock();
    // TODO: apply lemmas for the following
    reveal SeqToBV24();
    reveal BV24ToIndexSeq();
    reveal IndexSeqToBV24();
    reveal BV24ToSeq();
  }

  lemma DecodeEncodeBlock(s: seq<index>)
    requires |s| == 4
    ensures EncodeBlock(DecodeBlock(s)) == s
  {
    reveal EncodeBlock();
    reveal DecodeBlock();
    // TODO: apply lemmas for the following
    reveal SeqToBV24();
    reveal BV24ToIndexSeq();
    reveal IndexSeqToBV24();
    reveal BV24ToSeq();
  }

  opaque function DecodeRecursively(s: seq<index>): (b: seq<bv8>)
    requires |s| % 4 == 0
    decreases |s|
  {
    if |s| == 0 then []
    else DecodeBlock(s[..4]) + DecodeRecursively(s[4..])
  }

  lemma DecodeRecursivelyBounds(s: seq<index>)
    requires |s| % 4 == 0
    ensures |DecodeRecursively(s)| == |s| / 4 * 3
    ensures |DecodeRecursively(s)| % 3 == 0
    ensures |DecodeRecursively(s)| == 0 ==> |s| == 0
  {
    reveal DecodeRecursively();
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
      reveal DecodeRecursively();
    }
  }

  opaque function EncodeRecursively(b: seq<bv8>): (s: seq<index>)
    requires |b| % 3 == 0
    ensures |s| == |b| / 3 * 4
    ensures |s| % 4 == 0
  {
    if |b| == 0 then []
    else EncodeBlock(b[..3]) + EncodeRecursively(b[3..])
  }

  lemma EncodeRecursivelyBlock(b: seq<bv8>)
    requires |b| % 3 == 0
    ensures var s := EncodeRecursively(b); |s| != 0 ==> DecodeBlock(s[..4]) == b[..3]
  {
    if |b| == 0 {}
    else {
      EncodeDecodeBlock(b[..3]);
      reveal EncodeRecursively();
    }
  }

  lemma EncodeDecodeRecursively(b: seq<bv8>)
    requires |b| % 3 == 0
    ensures DecodeRecursively(EncodeRecursively(b)) == b
  {
    var s := EncodeRecursively(b);
    reveal EncodeRecursively();
    reveal DecodeRecursively();
    if |s| == 0 {
      assert |b| == 0;
    } else {
      // TODO: calc block?
      var bStart, bEnd := b[..3], b[3..];
      //assert s == EncodeBlock(bStart) + EncodeRecursively(bEnd);
      EncodeRecursivelyBlock(b);
      assert DecodeBlock(s[..4]) == bStart;
      EncodeDecodeRecursively(bEnd);
      //assert DecodeRecursively(EncodeRecursively(bEnd)) == bEnd;
    }
  }

  lemma DecodeEncodeRecursively(s: seq<index>)
    requires |s| % 4 == 0
    ensures (DecodeRecursivelyBounds(s); EncodeRecursively(DecodeRecursively(s)) == s)
  {
    var b := DecodeRecursively(s);
    if |s| == 0 {
      assert |b| == 0 by { reveal DecodeRecursively(); }
    } else {
      // TODO: simplify
      assert |b| != 0 by { reveal DecodeRecursively(); }
      DecodeRecursivelyBounds(s);
      assert EncodeRecursively(b) == EncodeBlock(b[..3]) + EncodeRecursively(b[3..]) by { reveal EncodeRecursively(); }
      assert DecodeRecursively(s) == DecodeBlock(s[..4]) + DecodeRecursively(s[4..]) by { reveal DecodeRecursively(); }
      assert (EncodeBlock(b[..3]) == s[..4]) by { DecodeRecursivelyBlock(s); }
      DecodeRecursivelyBounds(s[4..]);
      assert EncodeRecursively(DecodeRecursively(s[4..])) == s[4..] by { DecodeEncodeRecursively(s[4..]); }
      assert s == s[..4] + s[4..];
      //assert DecodeRecursively(s) == DecodeRecursively(s[..4] + s[4..]);
      //assert EncodeRecursively(DecodeRecursively(s)) == s;
    }
  }

  opaque function FromCharsToIndices(s: seq<char>): (b: seq<index>)
    requires forall k :: k in s ==> IsBase64Char(k)
    ensures |b| == |s|
  {
    seq(|s|, i requires 0 <= i < |s| => CharToIndex(s[i]))
  }

  opaque function FromIndicesToChars(b: seq<index>): (s: seq<char>)
    ensures forall k :: k in s ==> IsBase64Char(k)
    ensures |s| == |b|
  {
    seq(|b|, i requires 0 <= i < |b| => IndexToChar(b[i]))
  }

  lemma FromCharsToIndicesToChars(s: seq<char>)
    requires forall k :: k in s ==> IsBase64Char(k)
    ensures FromIndicesToChars(FromCharsToIndices(s)) == s
  {
    reveal FromIndicesToChars();
    reveal FromCharsToIndices();
    CharToIndexToCharAuto();
  }

  lemma FromIndicesToCharsToIndices(b: seq<index>)
    ensures FromCharsToIndices(FromIndicesToChars(b)) == b
  {
    reveal FromIndicesToChars();
    reveal FromCharsToIndices();
    IndexToCharToIndexAuto();
  }

  opaque function DecodeUnpadded(s: seq<char>): (b: seq<bv8>)
    requires IsUnpaddedBase64String(s)
  {
    reveal IsUnpaddedBase64String();
    DecodeRecursively(FromCharsToIndices(s))
  }

  lemma DecodeUnpaddedBounds(s: seq<char>)
    requires IsUnpaddedBase64String(s)
    ensures |DecodeUnpadded(s)| == |s| / 4 * 3
    ensures |DecodeUnpadded(s)| % 3 == 0
  {
    reveal DecodeUnpadded();
    reveal IsUnpaddedBase64String();
    reveal IsBase64String();
    var indices := FromCharsToIndices(s);
    assert |indices| == |s|;
    DecodeRecursivelyBounds(indices);
  }

  opaque function EncodeUnpadded(b: seq<bv8>): (s: seq<char>)
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
    reveal EncodeUnpadded();
    assert forall c :: c in s ==> IsBase64Char(c);
    assert IsBase64Char(s[|s| - 1]);
    assert s[|s| - 1] != '=' by { reveal IsBase64Char(); }
    reveal Is1Padding();
    reveal Is2Padding();
  }

  lemma EncodeUnpaddedBounds(b: seq<bv8>)
    requires |b| % 3 == 0
    ensures |EncodeUnpadded(b)| == |b| / 3 * 4
    ensures |EncodeUnpadded(b)| % 4 == 0
  {
    reveal EncodeUnpadded();
  }

  lemma EncodeUnpaddedBase64(b: seq<bv8>)
    requires |b| % 3 == 0
    ensures IsUnpaddedBase64String(EncodeUnpadded(b))
  {
    reveal EncodeUnpadded();
    reveal IsUnpaddedBase64String();
  }

  lemma EncodeDecodeUnpadded(b: seq<bv8>)
    requires |b| % 3 == 0
    ensures (EncodeUnpaddedBounds(b); EncodeUnpaddedBase64(b); DecodeUnpadded(EncodeUnpadded(b)) == b)
  {
    EncodeUnpaddedBase64(b);
    calc {
        DecodeUnpadded(EncodeUnpadded(b));
      == { reveal EncodeUnpadded(); }
        DecodeUnpadded(FromIndicesToChars(EncodeRecursively(b)));
      == { reveal DecodeUnpadded(); }
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
    reveal IsUnpaddedBase64String();
    var fromCharsToIndicesS := FromCharsToIndices(s);
    calc {
      EncodeUnpadded(DecodeUnpadded(s));
    == { reveal DecodeUnpadded(); }
      EncodeUnpadded(DecodeRecursively(FromCharsToIndices(s)));
    ==
      EncodeUnpadded(DecodeRecursively(fromCharsToIndicesS));
    == { reveal EncodeUnpadded(); }
      assert |fromCharsToIndicesS| % 4 == 0;
      /*assert |DecodeRecursively(fromCharsToIndicesS)| % 3 == 0 by {
        DecodeRecursivelyBounds(fromCharsToIndicesS);
      }*/
      FromIndicesToChars(EncodeRecursively(DecodeRecursively(fromCharsToIndicesS)));
    == { DecodeEncodeRecursively(fromCharsToIndicesS); }
      FromIndicesToChars(fromCharsToIndicesS);
    ==
      FromIndicesToChars(FromCharsToIndices(s));
    == { FromCharsToIndicesToChars(s); }
      s;
    }
  }

  opaque predicate Is1Padding(s: seq<char>) {
    |s| == 4 &&
    IsBase64Char(s[0]) &&
    IsBase64Char(s[1]) &&
    IsBase64Char(s[2]) &&
    // This is a result of the padded 0's in the sextet in the final element before the =
    CharToIndex(s[2]) & 0x3 == 0 && // Using & instead of % here makes the BV proofs easier
    s[3] == '='
  }

  opaque function Decode1Padding(s: seq<char>): (b: seq<bv8>)
    requires Is1Padding(s)
    // Padding with 1 = implies the sequence represents 2 bytes
    ensures |b| == 2
  {
    reveal Is1Padding();
    var d := DecodeBlock([CharToIndex(s[0]), CharToIndex(s[1]), CharToIndex(s[2]), 0]);
    [d[0], d[1]]
  }

  opaque function Encode1Padding(b: seq<bv8>): (s: seq<char>)
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

  lemma DecodeEncodeBlock1Padding(b: seq<bv8>)
    requires |b| == 2
    ensures
      var e := EncodeBlock([b[0], b[1], 0]);
      var d := DecodeBlock([e[0], e[1], e[2], 0]);
      [d[0], d[1]] == b
  {
    reveal EncodeBlock();
    reveal DecodeBlock();
    reveal BV24ToSeq();
    reveal SeqToBV24();
    reveal IndexSeqToBV24();
    reveal BV24ToIndexSeq();
    IndexToCharToIndexAuto();
    CharToIndexToCharAuto();
  }

  lemma Encode1PaddingIs1Padding(b: seq<bv8>)
    requires |b| == 2
    ensures Is1Padding(Encode1Padding(b))
  {
    // TODO: reduce resource use, brittleness
    reveal IndexToChar();
    reveal Is1Padding();
    reveal CharToIndex();
    reveal Encode1Padding();
    reveal EncodeBlock();
    reveal BV24ToSeq();
    reveal SeqToBV24();
    reveal IndexSeqToBV24();
    reveal BV24ToIndexSeq();
    reveal IsBase64Char();
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
      == { reveal Encode1Padding(); }
        Decode1Padding([IndexToChar(e[0]), IndexToChar(e[1]), IndexToChar(e[2]), '=']);
      == { reveal Decode1Padding(); }
        [d[0], d[1]];
      == { IndexToCharToIndex(e[0]); IndexToCharToIndex(e[1]); IndexToCharToIndex(e[2]); }
        [d'[0], d'[1]];
      == { DecodeEncodeBlock1Padding(b); }
        b;
    }
  }

  lemma {:vcs_split_on_every_assert} DecodeEncode1Padding(s: seq<char>)
    requires Is1Padding(s)
    ensures Encode1Padding(Decode1Padding(s)) == s
  {
    reveal Is1Padding();
    var d := DecodeBlock([CharToIndex(s[0]), CharToIndex(s[1]), CharToIndex(s[2]), 0]);
    var e := EncodeBlock([d[0], d[1], 0]);
    calc {
        Encode1Padding(Decode1Padding(s));
      == { reveal Decode1Padding(); }
        Encode1Padding([d[0], d[1]]);
      == { reveal Encode1Padding(); }
        [IndexToChar(e[0]), IndexToChar(e[1]), IndexToChar(e[2]), '='];
      == { 
           // TODO: make more readable, remove split
           reveal EncodeBlock();
           reveal DecodeBlock();
           reveal BV24ToSeq();
           reveal SeqToBV24();
           reveal IndexSeqToBV24();
           reveal BV24ToIndexSeq();
           IndexToCharToIndexAuto();
           CharToIndexToCharAuto();
         }
        s;
    }
  }

  opaque predicate Is2Padding(s: seq<char>) {
    |s| == 4 &&
    IsBase64Char(s[0]) &&
    IsBase64Char(s[1]) &&
    // This is a result of the padded 0's in the sextet in the final element before the two =
    CharToIndex(s[1]) % 0x10 == 0 &&
    s[2] == '=' &&
    s[3] == '='
  }

  opaque function Decode2Padding(s: seq<char>): (b: seq<bv8>)
    requires Is2Padding(s)
    // Padding with 2 = implies the sequence represents 1 byte
    ensures |b| == 1
  {
    reveal Is2Padding();
    var d := DecodeBlock([CharToIndex(s[0]), CharToIndex(s[1]), 0, 0]);
    [d[0]]
  }

  opaque function Encode2Padding(b: seq<bv8>): (s: seq<char>)
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
    reveal IndexToChar();
    reveal Is2Padding();
    reveal CharToIndex();
    reveal Encode2Padding();
    reveal EncodeBlock();
    reveal BV24ToSeq();
    reveal SeqToBV24();
    reveal IndexSeqToBV24();
    reveal BV24ToIndexSeq();
    reveal IsBase64Char();
  }

  lemma DecodeEncodeBlock2Padding(b: seq<bv8>)
    requires |b| == 1
    ensures
      var e := EncodeBlock([b[0], 0, 0]);
      var d := DecodeBlock([e[0], e[1], 0, 0]);
      [d[0]] == b
  {
    reveal EncodeBlock();
    reveal DecodeBlock();
    reveal BV24ToSeq();
    reveal SeqToBV24();
    reveal IndexSeqToBV24();
    reveal BV24ToIndexSeq();
    IndexToCharToIndexAuto();
    CharToIndexToCharAuto();
  }

  lemma EncodeDecode2Padding(b: seq<bv8>)
    requires |b| == 1
    ensures (Encode2PaddingIs2Padding(b); Decode2Padding(Encode2Padding(b)) == b)
  {
    Encode2PaddingIs2Padding(b);
    var e := EncodeBlock([b[0], 0, 0]);
    calc {
        Decode2Padding(Encode2Padding(b));
      == { reveal Encode2Padding(); }
        Decode2Padding([IndexToChar(e[0]), IndexToChar(e[1]), '=', '=']);
      == { reveal Decode2Padding(); }
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
    reveal Is2Padding();
    var s' := [CharToIndex(s[0]), CharToIndex(s[1]), 0, 0];
    var d := DecodeBlock(s');
    var e := EncodeBlock([d[0], 0, 0]);
    calc {
        Encode2Padding(Decode2Padding(s));
      == { reveal Decode2Padding(); }
        Encode2Padding([d[0]]);
      == { reveal Encode2Padding(); }
        [IndexToChar(e[0]), IndexToChar(e[1]), '=', '='];
      == {
           // TODO: make more readable
           reveal EncodeBlock();
           reveal DecodeBlock();
           reveal BV24ToSeq();
           reveal SeqToBV24();
           reveal IndexSeqToBV24();
           reveal BV24ToIndexSeq();
           IndexToCharToIndexAuto();
           CharToIndexToCharAuto();
         }
        s;
    }
  }

  opaque predicate IsBase64String(s: string) {
    // All Base64 strings are unpadded until the final block of 4 elements, where a padded seq could exist
    reveal IsUnpaddedBase64String();
    reveal Is2Padding();
    var finalBlockStart := |s| - 4;
    (|s| % 4 == 0) &&
      (IsUnpaddedBase64String(s) ||
      (IsUnpaddedBase64String(s[..finalBlockStart]) && (Is1Padding(s[finalBlockStart..]) || Is2Padding(s[finalBlockStart..]))))
  }

  opaque function DecodeValid(s: seq<char>): (b: seq<bv8>)
    requires IsBase64String(s)
  {
    reveal IsUnpaddedBase64String();
    reveal IsBase64String();
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

  opaque function DecodeValidLength(s: seq<char>): int
    requires s != []
    requires |s| % 4 == 0
  {
    var finalBlockStart := |s| - 4;
    var sSuffix := s[finalBlockStart..];
    if Is1Padding(sSuffix) then
      ((|s| - 4) / 4 * 3) + 2
    else if Is2Padding(sSuffix) then
      ((|s| - 4) / 4 * 3) + 1
    else
      |s| / 4 * 3
  }

  lemma DecodeValidHasExpectedLength(s: seq<char>)
    requires s != []
    requires |s| % 4 == 0
    requires IsBase64String(s)
    ensures |DecodeValid(s)| == DecodeValidLength(s)
  {
    reveal DecodeValidLength();
    reveal DecodeValid();
    reveal IsBase64String();
    var finalBlockStart := |s| - 4;
    var sPrefix, sSuffix := s[..finalBlockStart], s[finalBlockStart..];
    var b := DecodeValid(s);
    AboutDecodeValid(s, b);
    if Is1Padding (sSuffix) {
      DecodeUnpaddedBounds(sPrefix);
      assert |b| == ((|s| - 4) / 4 * 3) + 2;
    } else if Is2Padding(sSuffix) {
      DecodeUnpaddedBounds(sPrefix);
      assert |b| == ((|s| - 4) / 4 * 3) + 1;
    } else {
      DecodeUnpaddedBounds(s);
      assert |b| == |s| / 4 * 3;
    }
  }

  // TODO: simplify
  lemma EncodeDecodeValidLength(b: seq<bv8>)
    ensures (EncodeIsBase64(b); |DecodeValid(Encode(b))| == |b|)
  {
    var s := Encode(b);
    assert (b == []) <==> (s == []) by {
      EncodeLengthExact(b);
    }
    if s == [] {
      //assert Encode(b) == [] by  { EncodeLengthExact(b); }
      EncodeIsBase64(b);
      assert DecodeValid([]) == [] by { reveal DecodeValid(); }
      return;
    }
    EncodeIsBase64(b);
    reveal IsBase64String();
    //assert |s| >= 4 by { reveal IsBase64String(); }
    var finalBlockStart := |s| - 4;
    var prefix, suffix := s[..finalBlockStart], s[finalBlockStart..];
    var b' := DecodeValid(s);
    AboutDecodeValid(s, b');
    DecodeValidHasExpectedLength(s);
    assert |s| == if |b| % 3 == 0 then |b| / 3 * 4 else |b| / 3 * 4 + 4 by { EncodeLengthExact(b); }
    assert |b'| == DecodeValidLength(s);
    if |b'| % 3 == 0 {
      assert !Is1Padding(suffix);
      assert !Is2Padding(suffix);
      assert IsUnpaddedBase64String(s);
      assert |b'| == |s| / 4 * 3 by { reveal DecodeValidLength(); }
      if |b| % 3 == 0 {
      } else if |b| % 3 == 1 {
        // Contradiction
        EncodeIs2Padded(b);
        Encode2PaddingIs2Padding(b[(|b| - 1)..]);
      } else if |b| % 3 == 2 {
        // Contradiction
        EncodeIs1Padded(b);
        Encode1PaddingIs1Padding(b[(|b| - 2)..]);
      }
    } else if |b'| % 3 == 1 {
      assert Is2Padding(suffix);
      assert IsUnpaddedBase64String(prefix);
      assert |b'| == ((|s| - 4) / 4 * 3) + 1 by { reveal DecodeValidLength(); }
      if |b| % 3 == 0 {
        assert s == EncodeUnpadded(b) by { EncodeIsUnpadded(b); }
        EncodeUnpaddedNotPadded(b);
        if Is2Padding(suffix) {
          // Pattern for proof by contradiction without warnings
          assert false;
        }
      } else if |b| % 3 == 1 {
      } else if |b| % 3 == 2 {
        EncodeIs1Padded(b);
        Encode1PaddingIs1Padding(b[(|b| - 2)..]);
      }
    } else if |b'| % 3 == 2 {
      assert Is1Padding(suffix);
      assert IsUnpaddedBase64String(prefix);
      assert |b'| == ((|s| - 4) / 4 * 3) + 2 by { reveal DecodeValidLength(); }
      if |b| % 3 == 0 {
        assert s == EncodeUnpadded(b) by { EncodeIsUnpadded(b); }
        EncodeUnpaddedNotPadded(b);
        if Is1Padding(suffix) {
          // Pattern for proof by contradiction without warnings
          assert false;
        }
      } else if |b| % 3 == 1 {
        // Contradiction
        EncodeIs2Padded(b);
        Encode2PaddingIs2Padding(b[(|b| - 1)..]);
      } else if |b| % 3 == 2 {
      }
    }
  }

  lemma AboutDecodeValid(s: seq<char>, b: seq<bv8>)
    requires IsBase64String(s) && b == DecodeValid(s)
    ensures 4 <= |s| ==> var finalBlockStart := |s| - 4;
      var prefix, suffix := s[..finalBlockStart], s[finalBlockStart..];
      && (Is1Padding(suffix) && IsUnpaddedBase64String(prefix) <==> |b| % 3 == 2)
      && (Is2Padding(suffix) && IsUnpaddedBase64String(prefix) <==> |b| % 3 == 1)
      && (!Is1Padding(suffix) && !Is2Padding(suffix) && IsUnpaddedBase64String(s) <==> |b| % 3 == 0)
  {
    // TODO: reveal more locally
    reveal IsUnpaddedBase64String();
    reveal DecodeValid();
    reveal Decode1Padding();
    reveal IsBase64Char();
    reveal IsBase64String();
    reveal Is2Padding();
    reveal IndexToChar();
    if 4 <= |s| {
      var finalBlockStart := |s| - 4;
      var prefix, suffix := s[..finalBlockStart], s[finalBlockStart..];

      if s == [] {
      } else if Is1Padding(suffix) {
        assert !Is2Padding(suffix) by {
          reveal Is1Padding();
          reveal Is2Padding();
        }
        var x, y := DecodeUnpadded(prefix), Decode1Padding(suffix);
        assert b == x + y;
        assert |x| == |x| / 3 * 3 && |y| == 2 by {
          DecodeUnpaddedBounds(prefix);
        }
        Mod3(|x| / 3, |y|, |b|);
      } else if Is2Padding(suffix) {
        var x, y := DecodeUnpadded(prefix), Decode2Padding(suffix);
        assert b == x + y;
        assert |x| == |x| / 3 * 3 && |y| == 1 by {
          DecodeUnpaddedBounds(prefix);
        }
        Mod3(|x| / 3, |y|, |b|);
      } else {
        assert b == DecodeUnpadded(s);
        assert |b| % 3 == 0 by {
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

  opaque function Decode(s: seq<char>): (b: Result<seq<bv8>, string>)
    ensures IsBase64String(s) ==> b.Success? // Hard to use without this
  {
    if IsBase64String(s) then Success(DecodeValid(s)) else Failure("The encoding is malformed")
  }

  lemma DecodeFailure(s: seq<char>)
    ensures !IsBase64String(s) ==> Decode(s).Failure?
  {
    reveal Decode();
  }

  opaque ghost predicate StringIs7Bit(s: string) {
    forall c :: c in s ==> c < 128 as char
  }

  lemma UnpaddedBase64StringIs7Bit(s: string)
    requires IsUnpaddedBase64String(s)
    ensures StringIs7Bit(s)
  {
    reveal IsUnpaddedBase64String();
    reveal IsBase64Char();
    reveal StringIs7Bit();
  }

  lemma Is7Bit1Padding(s: string)
    requires Is1Padding(s)
    ensures StringIs7Bit(s)
  {
    reveal IsBase64Char();
    reveal Is1Padding();
    reveal StringIs7Bit();
  }

  lemma Is7Bit2Padding(s: string)
    requires Is2Padding(s)
    ensures StringIs7Bit(s)
  {
    reveal IsBase64Char();
    reveal Is2Padding();
    reveal StringIs7Bit();
  }

  lemma Base64StringIs7Bit(s: string)
    requires IsBase64String(s)
    ensures StringIs7Bit(s)
  {
    // TODO: simplify
    reveal IsBase64String();
    reveal IsBase64Char();
    var finalBlockStart := |s| - 4;
    if IsUnpaddedBase64String(s) {
      UnpaddedBase64StringIs7Bit(s);
    } else if finalBlockStart < 0 {
      reveal IsUnpaddedBase64String();
    } else {
      reveal IsUnpaddedBase64String();
      assert IsUnpaddedBase64String(s[..finalBlockStart]);
      UnpaddedBase64StringIs7Bit(s[..finalBlockStart]);
      assert StringIs7Bit(s[..finalBlockStart]);
      if (Is1Padding(s[finalBlockStart..])) {
        Is7Bit1Padding(s[finalBlockStart..]);
        assert StringIs7Bit(s[finalBlockStart..]);
      }
      if (Is2Padding(s[finalBlockStart..])) {
        Is7Bit2Padding(s[finalBlockStart..]);
        assert StringIs7Bit(s[finalBlockStart..]);
      }
      assert s == s[..finalBlockStart] + s[finalBlockStart..];
      reveal StringIs7Bit();
    }
  }

  // TODO: use
  lemma ConcatMod4Sequences<T>(s: seq<T>, t: seq<T>)
    requires |s| % 4 == 0
    requires |t| % 4 == 0
    ensures |s + t| % 4 == 0
  {
  }

  opaque function Encode(b: seq<bv8>): (s: seq<char>)
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

  lemma EncodeIsUnpadded(b: seq<bv8>)
    requires |b| % 3 == 0
    ensures Encode(b) == EncodeUnpadded(b)
    { reveal Encode(); }

  lemma EncodeIs2Padded(b: seq<bv8>)
    requires |b| % 3 == 1
    ensures Encode(b) == EncodeUnpadded(b[..(|b| - 1)]) + Encode2Padding(b[(|b| - 1)..])
    { reveal Encode(); }

  lemma EncodeIs1Padded(b: seq<bv8>)
    requires |b| % 3 == 2
    ensures Encode(b) == EncodeUnpadded(b[..(|b| - 2)]) + Encode1Padding(b[(|b| - 2)..])
    { reveal Encode(); }

  lemma EncodeLengthCongruentToZeroMod4(b: seq<bv8>)
    ensures |Encode(b)| % 4 == 0
  {
    reveal Encode();
    if |b| % 3 == 0 {
      EncodeUnpaddedBounds(b);
    } else if |b| % 3 == 1 {
      EncodeUnpaddedBounds(b[..(|b| - 1)]);
    } else {
      EncodeUnpaddedBounds(b[..(|b| - 2)]);
    }
  }

  lemma EncodeIsBase64(b: seq<bv8>)
    ensures IsBase64String(Encode(b))
  {
    // TODO: simplify
    reveal Encode();
    reveal IsBase64String();
    var s := Encode(b);
    EncodeLengthCongruentToZeroMod4(b);
    EncodeLengthExact(b);
    assert |s| >= 0;
    assert |s| % 4 == 0;
    var finalBlockStart := |s| - 4;
    if finalBlockStart < 0 {
      reveal IsUnpaddedBase64String();
      return;
    }
    var sStart := s[..finalBlockStart];
    var sEnd := s[finalBlockStart..];
    if |b| % 3 == 0 {
      assert s == EncodeUnpadded(b);
      EncodeUnpaddedBase64(b);
      assert IsUnpaddedBase64String(s);
      assert IsBase64String(s);
    } else if |b| % 3 == 1 {
      var bStart := b[..(|b| - 1)];
      var bEnd := b[(|b| - 1)..];
      assert s == EncodeUnpadded(bStart) + Encode2Padding(bEnd);
      assert s == sStart + sEnd;
      EncodeUnpaddedBounds(bStart);
      assert EncodeUnpadded(bStart) == sStart;
      assert Encode2Padding(bEnd) == sEnd;
      EncodeUnpaddedBase64(bStart);
      assert IsUnpaddedBase64String(sStart);
      Encode2PaddingIs2Padding(bEnd);
      assert Is2Padding(sEnd);
      assert IsBase64String(s);
    } else {
      var bStart := b[..(|b| - 2)];
      var bEnd := b[(|b| - 2)..];
      assert s == EncodeUnpadded(bStart) + Encode1Padding(bEnd);
      assert s == sStart + sEnd;
      EncodeUnpaddedBounds(bStart);
      assert EncodeUnpadded(bStart) == sStart;
      assert Encode1Padding(bEnd) == sEnd;
      EncodeUnpaddedBase64(bStart);
      assert IsUnpaddedBase64String(sStart);
      Encode1PaddingIs1Padding(bEnd);
      assert Is1Padding(sEnd);
      assert IsBase64String(s);
    }
  }

  lemma EncodeLengthExact(b: seq<bv8>)
    ensures var s := Encode(b);
      && (|b| % 3 == 0 ==> |s| == |b| / 3 * 4)
      && (|b| % 3 != 0 ==> |s| == |b| / 3 * 4 + 4)
  {
    reveal Encode();
    reveal Is1Padding();
    reveal Is2Padding();

    var s := Encode(b);
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

  lemma EncodeLengthBound(b: seq<bv8>)
    ensures var s := Encode(b);
      |s| <= |b| / 3 * 4 + 4
  {
    EncodeLengthExact(b);
  }

  // TODO: add wrappers for uint8

  // TODO: put lemmas here
}
