// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
#pragma warning disable CS0164 // This label has not been referenced
#pragma warning disable CS0162 // Unreachable code detected
#pragma warning disable CS1717 // Assignment made to same variable

namespace D2DPrettyPrinter {

  public partial class __default {
    public static Dafny.ISequence<Dafny.Rune> PrettyPrint(Dafny.ISequence<DAST._IModule> d)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Microsoft.Dafny.Compilers.WrapException.Throw();
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Not Implemented Yet");
      return s;
    }
  }
} // end of namespace D2DPrettyPrinter