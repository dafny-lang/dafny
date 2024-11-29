/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/**
  * The Unicode encoding scheme that serializes a UTF-8 code unit sequence in exactly the same order as the code unit
  * sequence itself.
  *
  * Because the UTF-8 encoding form deals in ordered byte sequences, the UTF-8 encoding scheme is trivial.
  * The byte ordering is completely defined by the UTF-8 code unit sequence itself.
  * We implement the encoding scheme here for completeness of the Unicode character encoding model,
  * and to perform the (trivial) conversion between `uint8`/`byte` and `bv8` values.
  *
  * (Section 3.10 D95)
  *
  * TODO: this should refine an abstract UnicodeEncodingScheme module
  * that states lemmas/conditions about Serialize and Deserialize
  * which refining modules would prove about their own implementations.
  */
module Std.Unicode.Utf8EncodingScheme {
  import opened Wrappers

  import BoundedInts
  import Collections.Seq
  import Utf8EncodingForm

  type byte = BoundedInts.uint8

  /**
    * Returns the byte serialization of the given code unit sequence.
    */
  function Serialize(s: Utf8EncodingForm.CodeUnitSeq): (b: seq<byte>)
  {
    Seq.Map(c => c as byte, s)
  }

  /**
    * Returns the code unit sequence that serializes to the given byte sequence.
    */
  function Deserialize(b: seq<byte>): (s: Utf8EncodingForm.CodeUnitSeq)
  {
    Seq.Map(b => b as Utf8EncodingForm.CodeUnit, b)
  }

  /**
    * Serializing a code unit sequence and then deserializing the result, yields the original code unit sequence.
    */
  lemma LemmaSerializeDeserialize(s: Utf8EncodingForm.CodeUnitSeq)
    ensures Deserialize(Serialize(s)) == s
  {}

  /**
    * Deserializing a byte sequence and then serializing the result, yields the original byte sequence.
    */
  @ResourceLimit("30e7")
  lemma LemmaDeserializeSerialize(b: seq<byte>)
    ensures Serialize(Deserialize(b)) == b
  {
    hide *;
    reveal BoundedInts.TWO_TO_THE_8;
    calc {
      Serialize(Deserialize(b));
    == // Definitions of Serialize, Deserialize
      { reveal Serialize; reveal Deserialize; }
      Seq.Map(c => c as byte, Seq.Map(b => b as Utf8EncodingForm.CodeUnit, b));
    == // Compositionality of Map
      Seq.Map(b => (b as Utf8EncodingForm.CodeUnit) as byte, b);
    == // Simplify map
      Seq.Map(b => b, b);
    == // Identity function
      b;
    }
  }
}
