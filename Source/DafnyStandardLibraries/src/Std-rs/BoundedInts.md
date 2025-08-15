
# The `BoundedInts` module

The `Std.BoundedInts` module contains definitions of types and constants for fixed-bit-width integers.

Dafny itself generally uses and reasons about mathematical, unbounded integers and natural numbers.
However compiled programs, for efficiency of computation and storage, will generally use fixed-bit-width
numbers. So Dafny defines them here, for use when needed.

An important implementation point about these type definitions is Dafny can determine which native type
in the target compiled program best matches the Dafny type. For example, the Dafny type `int16` is
a signed integer that fits in 16 bits. If a program using this type is compiled to, say Java, then
variables of this Dafny type will be compiled to Java `short` variables. In some cases there is no
natural match. For example Java does not have an unsigned 16-bit type while C# and C++ do.

This module defines:

- unsigned types of 8, 16, 32, 64, 128 bit widths (e.g. `uint32`)
- signed types of 8, 16, 32, 64, 128 bit widths (e.g. `int16`)
- unsigned types that are subsets of the corresponding signed type (e.g. `nat8` has values from 0 through 127)

The `natN` series of types require some care. A `nat8` for example has non-negative values up through 127,
that is, just 7-bits worth of values. But it can be directly converted to an `int8` and can be represented by a
native signed 8-bit integer type.

- if you need a general unsigned 8-bit type, with values running up to 256, use `uint8`
- if you want natural numbers that interact well with signed numbers and do not mind the restriction in range, use `nat8`
- if the target platform for compilation does not have native unsigned int types, then use nat types because of the smaller range

In addition, the module defines a number of constants that are powers of two (not all of them, just those that are generally useful).
They are useful in stating the ranges of fixed-bit-width integers. Examples are `TWO_TO_THE_15`, `TWO_TO_THE_32`.

Here are two example methods. In the first, the module `Std.BoundedInts` is renamed to `BI`, which is then used as the prefix for type and constant names.
In the second, the module is imported as opened, in which case the type and constant names can be used without qualification.
<!-- %check-verify -->
```dafny
module M {
  import BI = Std.BoundedInts
  method m(k: BI.int16) {
    assert k as int < BI.TWO_TO_THE_15;
  }
}

module N {
  import opened Std.BoundedInts

  method m(k: int16) {
    assert (k/256) as int < TWO_TO_THE_8;
  }
}
```
