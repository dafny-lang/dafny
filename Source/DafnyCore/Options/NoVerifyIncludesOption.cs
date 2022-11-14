namespace Microsoft.Dafny; 

public class NoVerifyIncludesOption : BooleanOption {
  public static readonly NoVerifyIncludesOption Instance = new(); 
  public override string LongName => "no-verify-includes";

  public override string Description => @"
(temporary) Do not verify included files unless they're also root input files.
This can be used when running a separate Dafny process on each
source file delivers better parallelization than when using a single process.
This option will be removed once all parts of the Dafny pipeline are parallelized.";
  
  public override string PostProcess(DafnyOptions options) {
    options.VerifyAllModules = !Get(options);
    return null;
  }
}