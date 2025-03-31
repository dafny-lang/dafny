# The `Ordinal` module

The `Ordinal` module defines several axioms and utilities for working with the `ORDINAL` type.

At the time of writing this, Dafny does not include that many operations and axioms
for working with ordinals.
Most of the axioms it does include only apply when `IsNat` is true for at least one argument.
This module includes several more that apply to all ordinals,
and defines the `Times` operation since multiplication with `*` is not currently supported.
These were invaluable in providing the foundation for the `Termination` module
and may be useful for other applications.
