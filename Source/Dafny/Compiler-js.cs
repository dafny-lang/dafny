//-----------------------------------------------------------------------------
//
// Copyright (C) Amazon.  All Rights Reserved.
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
  public class JavaScriptCompiler : Compiler {
    public JavaScriptCompiler(ErrorReporter reporter)
    : base(reporter) {
    }

    protected override void EmitHeader(Program program, TextWriter wr) {
    }
  }
}
