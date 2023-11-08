/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/
/**
XXX
*/
module {:options "-functionSyntax:4"} DafnyStdLibs.JSON.API {
  import opened BoundedInts
  import opened Errors
  import Values
  import Serializer
  import Deserializer
  import ZeroCopy = ZeroCopy.API

  function {:opaque} Serialize(js: Values.JSON) : (bs: SerializationResult<seq<byte>>)
  {
    var js :- Serializer.JSON(js);
    ZeroCopy.Serialize(js)
  }

  method SerializeAlloc(js: Values.JSON) returns (bs: SerializationResult<array<byte>>)
  {
    var js :- Serializer.JSON(js);
    bs := ZeroCopy.SerializeAlloc(js);
  }

  method SerializeInto(js: Values.JSON, bs: array<byte>) returns (len: SerializationResult<uint32>)
    modifies bs
  {
    var js :- Serializer.JSON(js);
    len := ZeroCopy.SerializeInto(js, bs);
  }

  function {:opaque} Deserialize(bs: seq<byte>) : (js: DeserializationResult<Values.JSON>)
  {
    var js :- ZeroCopy.Deserialize(bs);
    Deserializer.JSON(js)
  }
}