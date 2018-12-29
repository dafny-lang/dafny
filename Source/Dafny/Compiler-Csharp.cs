//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.IO;
using System.Diagnostics.Contracts;
using System.Text;


namespace Microsoft.Dafny {
  public class CsharpCompiler : Compiler {
    public CsharpCompiler(ErrorReporter reporter)
    : base(reporter) {
    }

    protected override void EmitHeader(Program program, TextWriter wr) {
      wr.WriteLine("// Dafny program {0} compiled into C#", program.Name);
      wr.WriteLine("// To recompile, use 'csc' with: /r:System.Numerics.dll");
      wr.WriteLine("// and choosing /target:exe or /target:library");
      wr.WriteLine("// You might also want to include compiler switches like:");
      wr.WriteLine("//     /debug /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162");
      wr.WriteLine();
      wr.WriteLine("using System;");
      wr.WriteLine("using System.Numerics;");
      EmitDafnySourceAttribute(program, wr);

      if (!DafnyOptions.O.UseRuntimeLib) {
        ReadRuntimeSystem(wr);
      }
    }

    void EmitDafnySourceAttribute(Program program, TextWriter wr) {
      Contract.Requires(program != null);

      wr.WriteLine("[assembly: DafnyAssembly.DafnySourceAttribute(@\"");

      var strwr = new StringWriter();
      strwr.NewLine = wr.NewLine;
      new Printer(strwr, DafnyOptions.PrintModes.Everything).PrintProgram(program, true);

      wr.Write(strwr.GetStringBuilder().Replace("\"", "\"\"").ToString());
      wr.WriteLine("\")]");
      wr.WriteLine();
    }

    void ReadRuntimeSystem(TextWriter wr) {
      string codebase = cce.NonNull(System.IO.Path.GetDirectoryName(cce.NonNull(System.Reflection.Assembly.GetExecutingAssembly().Location)));
      string path = System.IO.Path.Combine(codebase, "DafnyRuntime.cs");
      using (TextReader rd = new StreamReader(new FileStream(path, System.IO.FileMode.Open, System.IO.FileAccess.Read))) {
        while (true) {
          string s = rd.ReadLine();
          if (s == null)
            return;
          wr.WriteLine(s);
        }
      }
    }

  }
}
