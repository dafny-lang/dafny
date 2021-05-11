using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Text;

namespace Microsoft.Dafny
{
  static class ConcreteSyntaxTreeFormatProvider
  {
    static void FormatError()
    {
      throw new FormatException("Format string was invalid");
    }
    
  }
}