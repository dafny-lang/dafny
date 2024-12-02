/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**
 The low-level (zero-copy) API of the JSON library. This version is efficient, verified and allows incremental
 changes, but is more cumbersome to use. This API operates on concrete syntax trees that capture details of 
 punctuation and blanks and represent strings using unescaped, undecoded utf-8 byte sequences.
 */
module Std.JSON.ZeroCopy.API {
  import Grammar
  import ConcreteSyntax.Spec
  import Serializer
  import Deserializer
  import opened BoundedInts
  import opened Wrappers
  import opened Errors


  /* Serialization (JSON syntax trees to utf-8 bytes) */
  function Serialize(js: Grammar.JSON) : (bs: SerializationResult<seq<byte>>)
    ensures bs == Success(Spec.JSON(js))
  {
    Success(Serializer.Text(js).Bytes())
  }

  method SerializeAlloc(js: Grammar.JSON) returns (bs: SerializationResult<array<byte>>)
    ensures bs.Success? ==> fresh(bs.value)
    ensures bs.Success? ==> bs.value[..] == Spec.JSON(js)
  {
    bs := Serializer.Serialize(js);
  }

  method SerializeInto(js: Grammar.JSON, bs: array<byte>) returns (len: SerializationResult<uint32>)
    modifies bs
    ensures len.Success? ==> len.value as int <= bs.Length
    ensures len.Success? ==> bs[..len.value] == Spec.JSON(js)
    ensures len.Success? ==> bs[len.value..] == old(bs[len.value..])
    ensures len.Failure? ==> unchanged(bs)
  {
    len := Serializer.SerializeTo(js, bs);
  }

  /* Deserialization (utf-8 bytes to JSON syntax trees) */
  function Deserialize(bs: seq<byte>) : (js: DeserializationResult<Grammar.JSON>)
    ensures js.Success? ==> bs == Spec.JSON(js.value)
  {
    Deserializer.API.OfBytes(bs)
  }
}