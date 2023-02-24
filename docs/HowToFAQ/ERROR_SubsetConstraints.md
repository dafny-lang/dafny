---
title: "Error: value does not satisfy the subset constraints of '(seq<uint8>, Materials.EncryptedDataKey) -> seq<uint8>' (possible cause: it may be partial or have read effects)"
---

Here is an example of submitted code that produced this error:
```dafny
function EncryptedDataKeys(edks: Msg.EncryptedDataKeys):  (ret: seq<uint8>)
  requires edks.Valid()
{
    UInt16ToSeq(|edks.entries| as uint16) + FoldLeft(FoldEncryptedDataKey, [], edks.entries)
}

function FoldEncryptedDataKey(acc: seq<uint8>, edk: Materials.EncryptedDataKey): (ret: seq<uint8>)
  requires edk.Valid()
{
    acc + edk.providerID + edk.providerInfo + edk.ciphertext
}
```

The general cause of this error is supplying some value to a situation where (a) the type of the target (declared variable, formal argument) is a subset type and (b) Dafny cannot prove that the value falls within the predicate for the subset type. In this example code, `uint8` is likely a subset type and could be at fault here.
But more likely and less obvious is supplying `FoldEncryptedDataKey` as the actual argument to `FoldLeft`.

The signature of `FoldLeft` is `function {:opaque} FoldLeft<A,T>(f: (A, T) -> A, init: A, s: seq<T>): A`.
Note that the type of the function uses a `->` arrow, namely a total, heap-independent function (no requires or reads clause).
But `FoldEncryptedDataKey` does have a requires clause. Since `->` functions are a subset type of partial, heap-dependent `~>` functions,
the error message complains about the subset type constraints not being satisfied.

These various arrow types are described in the [release notes](https://github.com/dafny-lang/dafny/releases/tag/v2.0.0)
when they were first added to the language. They are also documented in the [reference manual](../DafnyRef/DafnyRef#sec-arrow-types).
