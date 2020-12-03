<p></p> <!-- avoids duplicate title -->  

# Dafny compilation to C++

The C++ backend was written assuming that it would primarily support writing
C/C++ style code in Dafny, which leads to some limitations in the current
implementation.

- We do not support BigIntegers, so do not use `int`, or raw instances of
  `arr.Length`, or sequence length, etc. in executable code.  You can however,
  use `arr.Length as uint64` if you can prove your array is an appropriate
  size.  The compiler will report inappropriate integer use.
- We do not support more advanced Dafny features like traits or co-inductive
  types.
- Very limited support for higher order functions even for array init.  Use
  extern definitions like newArrayFill (see extern.dfy) or similar.  See also
  the example in `functions.dfy`.
- We currently only support tuples up to arity 5.  A common place where you
  might go over that limit is print statements, which tuple the arguments.
- The current backend also assumes the use of C++17 in order to cleanly and
  performantly implement datatypes.

