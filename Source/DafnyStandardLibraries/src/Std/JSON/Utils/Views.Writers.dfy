/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**
 Implements slices (`Chain`s) over byte strings whose bounds are representable as `int32` native integers (`View`s).
 */
module Std.JSON.Utils.Views.Writers {
  import opened BoundedInts
  import opened Wrappers
  import opened Core

  datatype Chain =
    | Empty
    | Chain(previous: Chain, v: View)
  {
    function Length() : nat {
      if Empty? then 0
      else previous.Length() + v.Length() as int
    }

    function Count() : nat {
      if Empty? then 0
      else previous.Count() + 1
    }

    function Bytes() : (bs: bytes)
      ensures |bs| == Length()
    {
      if Empty? then []
      else previous.Bytes() + v.Bytes()
    }

    function Append(v': View): (c: Chain)
      ensures c.Bytes() == Bytes() + v'.Bytes()
    {
      if Chain? && Adjacent(v, v') then
        Chain(previous, Merge(v, v'))
      else
        Chain(this, v')
    }

    @TailRecursion
    method CopyTo(dest: array<byte>, end: uint32)
      requires end as int == Length() <= dest.Length
      modifies dest
      ensures dest[..end] == Bytes()
      ensures dest[end..] == old(dest[end..])
    {
      if Chain? {
        var end := end - v.Length();
        v.CopyTo(dest, end);
        previous.CopyTo(dest, end);
      }
    }
  }

  type Writer = w: Writer_ | w.Valid? witness Writer(0, Chain.Empty)
  datatype Writer_ = Writer(length: uint32, chain: Chain)
  {
    static const Empty: Writer := Writer(0, Chain.Empty)

    const Empty? := chain.Empty?
    const Unsaturated? := length != UINT32_MAX

    ghost function Length() : nat { chain.Length() }

    ghost const Valid? :=
      length == // length is a saturating counter
      if chain.Length() >= TWO_TO_THE_32 then UINT32_MAX
      else chain.Length() as uint32

    function Bytes() : (bs: bytes)
      ensures |bs| == Length()
    {
      chain.Bytes()
    }

    static function SaturatedAddU32(a: uint32, b: uint32): uint32 {
      if a <= UINT32_MAX - b then a + b
      else UINT32_MAX
    }

    function Append(v': View): (rw: Writer)
      requires Valid?
      ensures rw.Unsaturated? <==> v'.Length() < UINT32_MAX - length
      ensures rw.Bytes() == Bytes() + v'.Bytes()
    {
      Writer(SaturatedAddU32(length, v'.Length()),
             chain.Append(v'))
    }

    function Then(fn: Writer ~> Writer) : Writer
      reads fn.reads(this)
      requires Valid?
      requires fn.requires(this)
    {
      fn(this)
    }

    @TailRecursion
    method CopyTo(dest: array<byte>)
      requires Valid?
      requires Unsaturated?
      requires Length() <= dest.Length
      modifies dest
      ensures dest[..length] == Bytes()
      ensures dest[length..] == old(dest[length..])
    {
      chain.CopyTo(dest, length);
    }

    method ToArray() returns (bs: array<byte>)
      requires Valid?
      requires Unsaturated?
      ensures fresh(bs)
      ensures bs[..] == Bytes()
    {
      bs := new byte[length](i => 0);
      CopyTo(bs);
    }
  }
}