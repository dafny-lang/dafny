/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**
 The high-level API of the JSON library. This version is built on top of the low-level (zero-copy) API.
 This API is more convenient to use, but it is unverified and less efficient. It produces abstract datatype 
 value trees that represent strings using Dafny's built-in `string` type.
 */
module Std.JSON.API {
  import Values
  import Serializer
  import Deserializer
  import ZeroCopy = ZeroCopy.API
  import opened BoundedInts
  import opened Errors

  /* Serialization (JSON values to utf-8 bytes) */
  function Serialize(js: Values.JSON) : (bs: SerializationResult<seq<byte>>) {
    var js :- Serializer.JSON(js);
    ZeroCopy.Serialize(js)
  }

  method SerializeAlloc(js: Values.JSON) returns (bs: SerializationResult<array<byte>>) {
    var js :- Serializer.JSON(js);
    bs := ZeroCopy.SerializeAlloc(js);
  }

  method SerializeInto(js: Values.JSON, bs: array<byte>) returns (len: SerializationResult<uint32>)
    modifies bs
  {
    var js :- Serializer.JSON(js);
    len := ZeroCopy.SerializeInto(js, bs);
  }

  /* Deserialization (utf-8 bytes to JSON values) */
  function Deserialize(bs: seq<byte>) : (js: DeserializationResult<Values.JSON>) {
    var js :- ZeroCopy.Deserialize(bs);
    Deserializer.JSON(js)
  }
}