module Base64Examples {
  import opened Std.Base64
  import opened Std.BoundedInts
  import opened Std.Wrappers

  method CheckEncodeDecode(uints: seq<uint8>, bytes: seq<bv8>) {
    expect Decode(Encode(uints)) == Success(uints);
    expect DecodeBV(EncodeBV(bytes)) == Success(bytes);
  }

  method {:test} TestRoundTripEmpty() {
    CheckEncodeDecode([], []);
  }

  method {:test} TestRoundTripOne() {
    CheckEncodeDecode([0], [0]);
  }

  method {:test} TestRoundTripTwo() {
    CheckEncodeDecode([1, 2], [3, 4]);
  }

  method {:test} TestRoundTripThree() {
    CheckEncodeDecode([112, 234], [43, 76]);
  }

  method {:test} TestRoundTripMedium() {
    var medUints := seq(512, i => (i % 256) as uint8);
    var medBytes := seq(512, i => (i % 256) as bv8);
    CheckEncodeDecode(medUints, medBytes);
  }

  // TODO: even this size is too big to practically test for Go and JS
  /*
  method {:test} TestRoundTripBig() {
    // Larger sizes are unfortunately pretty slow. An
    // optimized implementation seems worthwhile.
    var bigUints := seq(438530, _ => 76);
    var bigBytes := seq(438530, _ => 45);
    CheckEncodeDecode(bigUints, bigBytes);
  }
  */

  method {:test} TestDecodeFail() {
    expect Decode("$&^*(_)").Failure?;
  }
}
