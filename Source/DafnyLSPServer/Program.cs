using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO.Pipelines;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LSPServer
{
  class Program
  {
    static void Main(string[] args)
    {
      var reader = PipeReader.Create(Console.OpenStandardInput());
      var writer = PipeWriter.Create(Console.OpenStandardOutput());

      DafnyLSPServer.Start(reader, writer).Wait();
      Process.GetCurrentProcess().WaitForExit();
    }
  }
}
