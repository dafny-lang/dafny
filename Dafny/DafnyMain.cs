//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.IO;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class Main {
    /// <summary>
    /// Returns null on success, or an error string otherwise.
    /// </summary>
    public static string ParseCheck(List<string/*!*/>/*!*/ fileNames, string/*!*/ programName, out Program program)
      //modifies Bpl.CommandLineOptions.Clo.XmlSink.*;
    {
      Contract.Requires(programName != null);
      Contract.Requires(fileNames != null);
      program = null;
      List<ModuleDecl> modules = new List<ModuleDecl>();
      BuiltIns builtIns = new BuiltIns();
      foreach (string dafnyFileName in fileNames){
        Contract.Assert(dafnyFileName != null);
        if (Bpl.CommandLineOptions.Clo.XmlSink != null && Bpl.CommandLineOptions.Clo.XmlSink.IsOpen) {
          Bpl.CommandLineOptions.Clo.XmlSink.WriteFileFragment(dafnyFileName);
        }
        if (Bpl.CommandLineOptions.Clo.Trace) 
        {
          Console.WriteLine("Parsing " + dafnyFileName);
        }

        int errorCount;
        try 
        {
          errorCount = Dafny.Parser.Parse(dafnyFileName, modules, builtIns);
          if (errorCount != 0) 
          {
            return string.Format("{0} parse errors detected in {1}", errorCount, dafnyFileName);
          }
        } 
        catch (IOException e) 
        {
          return string.Format("Error opening file \"{0}\": {1}", dafnyFileName, e.Message);
        }
      }

      program = new Program(programName, modules, builtIns);

      if (Bpl.CommandLineOptions.Clo.DafnyPrintFile != null) {
        string filename = Bpl.CommandLineOptions.Clo.DafnyPrintFile;
        if (filename == "-") {
          Printer pr = new Printer(System.Console.Out);
          pr.PrintProgram(program);
        } else {
          using (TextWriter writer = new System.IO.StreamWriter(filename)) {
            Printer pr = new Printer(writer);
            pr.PrintProgram(program);
          }
        }
      }
      
      if (Bpl.CommandLineOptions.Clo.NoResolve || Bpl.CommandLineOptions.Clo.NoTypecheck) { return null; }

      Dafny.Resolver r = new Dafny.Resolver(program);
      r.ResolveProgram(program);
      if (r.ErrorCount != 0) {
        return string.Format("{0} resolution/type errors detected in {1}", r.ErrorCount, programName);
      }

      return null;  // success
    }
  }
}