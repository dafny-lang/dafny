namespace Microsoft.Dafny;

class CompileOption : NaturalNumberOption {
  public static readonly CompileOption Instance = new();

  public override object DefaultValue
  {
    get { return 999; }
  }

  public override string TypedPostProcess(DafnyOptions options, uint value) {
    var compile = value;

    if (compile != 999) {
      // convert option to two booleans
      options.EmitExecutable = compile != 0;
      options.ForceCompile = compile == 2 || compile == 4;
      options.RunAfterCompile = compile == 3 || compile == 4;
    }
    return base.TypedPostProcess(options, value);
  }

  public override string LongName => "compile";
  public override string ShortName => null;
  public override string ArgumentName => null;
  public override string Category => "Compilation options";

  public override string Description => @"
0 - do not compile Dafny program
1 (default) - upon successful verification of the Dafny
    program, compile it to the designated target language
    (/noVerify automatically counts as failed verification)
2 - always attempt to compile Dafny program to the target
    language, regardless of verification outcome
3 - if there is a Main method and there are no verification
    errors and /noVerify is not used, compiles program in
    memory (i.e., does not write an output file) and runs it
4 - like (3), but attempts to compile and run regardless of
    verification outcome".TrimStart();
}
