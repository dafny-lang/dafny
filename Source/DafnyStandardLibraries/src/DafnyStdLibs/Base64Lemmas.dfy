// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

module Base64Lemmas {
  import opened DafnyStdLibs.Wrappers
  import opened DafnyStdLibs.BoundedInts
  import opened Base64

  lemma SeqPartsMakeWhole<T>(s: seq<T>, i: nat)
    requires i <= |s|
    ensures s[..i] + s[i..] == s
  {}

  lemma DecodeValidEncodeEmpty(s: seq<char>)
    requires s == []
    ensures reveal IsUnpaddedBase64String(); reveal IsBase64String(); Encode(DecodeValid(s)) == s
  {
    assert IsBase64String(s) by { reveal IsBase64String(); reveal IsUnpaddedBase64String(); }
    var b := DecodeValid(s);
    assert b == [] by { reveal DecodeValid(); }
    assert Encode(b) == [] by {
      reveal Encode();
      reveal EncodeUnpadded();
      reveal EncodeRecursively();
      reveal FromIndicesToChars();
    }
  }

  lemma EncodeDecodeValidEmpty(b: seq<bv8>)
    requires b == []
    ensures (EncodeIsBase64(b) ; DecodeValid(Encode(b)) == b)
  {
    assert Encode(b) == [] by {
      reveal Encode();
      reveal EncodeUnpadded();
      reveal EncodeRecursively();
      reveal FromIndicesToChars();
    }
    EncodeIsBase64(b);
    assert DecodeValid([]) == [] by {
      reveal DecodeValid();
    }
  }

  lemma DecodeValidEncodeUnpadded(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires !Is1Padding(s[(|s| - 4)..])
    requires !Is2Padding(s[(|s| - 4)..])
    ensures Encode(DecodeValid(s)) == s
  {
    reveal Encode();
    reveal DecodeValid();
    reveal IsBase64String();
    DecodeUnpaddedBounds(s);
    calc {
      Encode(DecodeValid(s));
    ==
      Encode(DecodeUnpadded(s));
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
      var s := Encode(b);
      && IsUnpaddedBase64String(s)
      && |s| >= 4
      && !Is1Padding(s[(|s| - 4)..])
      && !Is2Padding(s[(|s| - 4)..])
      && s == EncodeUnpadded(b)
  {
    EncodeUnpaddedBase64(b);
    EncodeUnpaddedBounds(b);
    var s := Encode(b);
    assert s == EncodeUnpadded(b) by { EncodeIsUnpadded(b); }
    assert !Is1Padding(s[(|s| - 4)..]) by { EncodeUnpaddedNotPadded(b); }
    assert !Is2Padding(s[(|s| - 4)..]) by { EncodeUnpaddedNotPadded(b); }
  }

  lemma EncodeDecodeValid2Padded(b: seq<bv8>)
    requires |b| % 3 == 1
    ensures
       var s := Encode(b);
       && s == (EncodeUnpadded(b[..(|b| - 1)]) + Encode2Padding(b[(|b| - 1)..]))
       && Is2Padding(s[(|s| - 4)..])
  {
    EncodeUnpaddedBase64(b[..(|b| - 1)]);
    EncodeUnpaddedBounds(b[..(|b| - 1)]);
    reveal Encode();
    var s := Encode(b);
    Encode2PaddingIs2Padding(b[(|b| - 1)..]);
    assert Is2Padding(s[(|s| - 4)..]);
  }

  lemma EncodeDecodeValid1Padded(b: seq<bv8>)
    requires |b| % 3 == 2
    ensures
      var s := Encode(b);
      && s == (EncodeUnpadded(b[..(|b| - 2)]) + Encode1Padding(b[(|b| - 2)..]))
      && |s| >= 4
      && IsUnpaddedBase64String(s[..(|s| - 4)])
      && Is1Padding(s[(|s| - 4)..])
  {
    EncodeUnpaddedBase64(b[..(|b| - 2)]);
    EncodeUnpaddedBounds(b[..(|b| - 2)]);
    reveal Encode();
    var s := Encode(b);
    Encode1PaddingIs1Padding(b[(|b| - 2)..]);
    assert Is1Padding(s[(|s| - 4)..]);
  }


  lemma DecodeValidUnpaddedPartialFrom1PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[(|s| - 4)..])
    ensures reveal IsUnpaddedBase64String(); reveal IsBase64String(); reveal DecodeValid(); DecodeValid(s)[..(|DecodeValid(s)| - 2)] == DecodeUnpadded(s[..(|s| - 4)])
  {
    reveal IsBase64String();
    reveal DecodeValid();
  }

  lemma DecodeValid1PaddedPartialFrom1PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[(|s| - 4)..])
    ensures reveal DecodeValid(); DecodeValid(s)[(|DecodeValid(s)| - 2)..] == Decode1Padding(s[(|s| - 4)..])
  {
    reveal DecodeValid();
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

  lemma DecodeValidEncode1Padding(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[(|s| - 4)..])
    ensures Encode(DecodeValid(s)) == s
  {
    assert |DecodeValid(s)| % 3 == 2 by { DecodeValid1PaddingLengthMod3(s); }
    calc {
      Encode(DecodeValid(s));
    == { reveal Encode(); }
      EncodeUnpadded(DecodeValid(s)[..(|DecodeValid(s)| - 2)]) + Encode1Padding(DecodeValid(s)[(|DecodeValid(s)| - 2)..]);
    == { DecodeValidUnpaddedPartialFrom1PaddedSeq(s); reveal IsBase64String(); reveal IsUnpaddedBase64String(); }
      EncodeUnpadded(DecodeUnpadded(s[..(|s| - 4)])) + Encode1Padding(DecodeValid(s)[(|DecodeValid(s)| - 2)..]);
    == { reveal IsUnpaddedBase64String(); DecodeEncodeUnpadded(s[..(|s| - 4)]); }
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
      (reveal IsUnpaddedBase64String();
       reveal DecodeValid();
       reveal IsBase64String();
       var b := DecodeValid(s);
       b[..(|b| - 1)] == DecodeUnpadded(s[..(|s| - 4)]) &&
       b[(|b| - 1)..] == Decode2Padding(s[(|s| - 4)..]))
  {
    reveal IsUnpaddedBase64String();
    reveal IsBase64String();
    reveal DecodeValid();
    AboutDecodeValid(s, DecodeValid(s));
    assert Is2Padding(s[(|s| - 4)..]);
  }

  lemma DecodeValidPartialsFrom1PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[(|s| - 4)..])
    ensures 
      (reveal IsUnpaddedBase64String();
       reveal DecodeValid();
       reveal IsBase64String();
       var b := DecodeValid(s);
       b[..(|b| - 2)] == DecodeUnpadded(s[..(|s| - 4)]) &&
       b[(|b| - 2)..] == Decode1Padding(s[(|s| - 4)..]))
  {
    reveal IsUnpaddedBase64String();
    reveal DecodeValid();
    reveal IsBase64String();
    AboutDecodeValid(s, DecodeValid(s));
  }

  lemma UnpaddedBase64Prefix(s: string)
    requires IsBase64String(s)
    requires |s| >= 4
    ensures IsUnpaddedBase64String(s[..(|s| - 4)])
  {
    reveal IsBase64String();
    reveal IsUnpaddedBase64String();
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
    ensures Encode(DecodeValid(s)) == s
  {
    assert |DecodeValid(s)| % 3 == 1 by { DecodeValid2PaddingLengthMod3(s); }
    calc {
      Encode(DecodeValid(s));
    == { reveal Encode(); }
      EncodeUnpadded(DecodeValid(s)[..(|DecodeValid(s)| - 1)]) + Encode2Padding(DecodeValid(s)[(|DecodeValid(s)| - 1)..]);
    == { DecodeValidPartialsFrom2PaddedSeq(s); reveal IsUnpaddedBase64String(); reveal IsBase64String(); }
      EncodeUnpadded(DecodeUnpadded(s[..(|s| - 4)])) + Encode2Padding(DecodeValid(s)[(|DecodeValid(s)| - 1)..]);
    == { reveal IsBase64String(); DecodeEncodeUnpadded(s[..(|s| - 4)]); }
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
    ensures Encode(DecodeValid(s)) == s
  {
    reveal IsBase64String();
    if s == [] {
      calc {
        Encode(DecodeValid(s));
      == { DecodeValidEncodeEmpty(s); }
        s;
      }
    } else if |s| >= 4 && Is1Padding(s[(|s| - 4)..]) {
      calc {
        Encode(DecodeValid(s));
      == { DecodeValidEncode1Padding(s); }
        s;
      }
    } else if |s| >= 4 && Is2Padding(s[(|s| - 4)..]) {
      calc {
        Encode(DecodeValid(s));
      == { DecodeValidEncode2Padding(s); }
        s;
      }
    } else {
      calc {
        Encode(DecodeValid(s));
      == { DecodeValidEncodeUnpadded(s); }
        s;
      }
    }
  }

  lemma EncodeDecodeValid(b: seq<bv8>)
    ensures (EncodeIsBase64(b); DecodeValid(Encode(b)) == b)
  {
    EncodeIsBase64(b);
    var s := Encode(b);
    if b == [] {
      calc {
        DecodeValid(Encode(b));
      == { EncodeDecodeValidEmpty(b); }
        b;
      }
    } else if |b| % 3 == 0 {
      calc {
        DecodeValid(Encode(b));
      == { EncodeIsUnpadded(b); } 
        DecodeValid(EncodeUnpadded(b));
      == { EncodeDecodeValidUnpadded(b); reveal DecodeValid(); }
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
        DecodeValid(Encode(b));
      == { reveal Encode(); }
        DecodeValid(EncodeUnpadded(prefix) + Encode2Padding(suffix));
      == { reveal DecodeValid(); DecodeValidPartialsFrom2PaddedSeq(s); }
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
        DecodeValid(Encode(b));
      == { reveal Encode(); }
        DecodeValid(EncodeUnpadded(prefix) + Encode1Padding(suffix));
      == { reveal DecodeValid(); DecodeValidPartialsFrom1PaddedSeq(s); }
        DecodeUnpadded(EncodeUnpadded(prefix)) + Decode1Padding(Encode1Padding(suffix));
      == { EncodeDecodeUnpadded(prefix); EncodeDecode1Padding(suffix); }
        prefix + suffix;
      ==
        b;
      }
    }
  }

  lemma DecodeEncode(s: seq<char>)
    requires IsBase64String(s)
    ensures Encode(Decode(s).value) == s
  {
    reveal Decode();
    calc {
      Encode(Decode(s).value);
    == { DecodeValidEncode(s); }
      s;
    }
  }

  lemma EncodeDecode(b: seq<bv8>)
    ensures Decode(Encode(b)) == Success(b)
  {
    reveal Decode();
    EncodeIsBase64(b);
    calc {
      Decode(Encode(b));
    == { assert IsBase64String(Encode(b)); }
      Success(DecodeValid(Encode(b)));
    == { EncodeDecodeValid(b); }
      Success(b);
    }
  }
}
