/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/
/**
XXX
*/
module {:options "-functionSyntax:4"} DafnyStdLibs.JSON.ZeroCopy.API {
  import opened BoundedInts
  import opened Wrappers
  import opened Errors
  import Grammar
  import ConcreteSyntax.Spec
  import Serializer
  import Deserializer

  function {:opaque} Serialize(js: Grammar.JSON) : (bs: SerializationResult<seq<byte>>)
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

  function {:opaque} Deserialize(bs: seq<byte>) : (js: DeserializationResult<Grammar.JSON>)
    ensures js.Success? ==> bs == Spec.JSON(js.value)
  {
    Deserializer.API.OfBytes(bs)
  }
}