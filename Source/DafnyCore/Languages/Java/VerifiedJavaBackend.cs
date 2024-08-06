using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.CommandLine;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using DafnyCore;
using DafnyCore.Options;

namespace Microsoft.Dafny.Compilers;

public class VerifiedJavaBackend : JavaBackend {

  public override string TargetId => "vjava";
  
  public override void Compile(Program dafnyProgram, string dafnyProgramName, ConcreteSyntaxTree output) {
    ProcessTranslationRecords(dafnyProgram, dafnyProgramName, output);
    CheckInstantiationReplaceableModules(dafnyProgram);
    ProcessOuterModules(dafnyProgram);

    CodeGenerator.Compile(dafnyProgram, output);
  }
  
  public VerifiedJavaBackend(DafnyOptions options) : base(options) {
  }
}
