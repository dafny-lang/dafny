// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
#pragma warning disable CS0164 // This label has not been referenced
#pragma warning disable CS0162 // Unreachable code detected
#pragma warning disable CS1717 // Assignment made to same variable

namespace DafnyToRustCompilerCoverage {

  public partial class __default {
    public static void TestIsCopy()
    {
      if (!(Defs.__default.IsNewtypeCopy(DAST.NewtypeRange.create_Bool()))) {
        throw new Dafny.HaltException("Backends/Rust/Dafny-compiler-rust-coverage.dfy(9,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      if (!(Defs.__default.IsNewtypeCopy(DAST.NewtypeRange.create_U128(true)))) {
        throw new Dafny.HaltException("Backends/Rust/Dafny-compiler-rust-coverage.dfy(10,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      if (!(Defs.__default.IsNewtypeCopy(DAST.NewtypeRange.create_U128(false)))) {
        throw new Dafny.HaltException("Backends/Rust/Dafny-compiler-rust-coverage.dfy(11,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      if (!(!(Defs.__default.IsNewtypeCopy(DAST.NewtypeRange.create_BigInt())))) {
        throw new Dafny.HaltException("Backends/Rust/Dafny-compiler-rust-coverage.dfy(12,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      if (!(!(Defs.__default.IsNewtypeCopy(DAST.NewtypeRange.create_NoRange())))) {
        throw new Dafny.HaltException("Backends/Rust/Dafny-compiler-rust-coverage.dfy(13,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
    }
  }
} // end of namespace DafnyToRustCompilerCoverage