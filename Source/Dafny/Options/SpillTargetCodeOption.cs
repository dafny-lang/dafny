namespace Microsoft.Dafny;

// TODO remove and use old code.
class SpillTargetCodeOption : NaturalNumberOption {
  public static readonly SpillTargetCodeOption Instance = new();

  public override object DefaultValue => 0U;

  public override string PostProcess(DafnyOptions options) {
    options.SpillTargetCode = Get(options);
    return null;
  }

  public override string LongName => "spillTargetCode";

  public override string ShortName => null;
  public override string ArgumentName => null;
  public override string Category => "Compilation options";

  public override string Description => @"
This option concerns the textual representation of the target program.
This representation is of no interest when working with only Dafny code,
but may be of interest in cross-language situations.
0 (default) - Don't make any extra effort to write the textual target program
    (but still compile it, if /compile indicates to do so).
1 - Write the textual target program, if it is being compiled.
2 - Write the textual target program, provided it passes the verifier (and
    /noVerify is NOT used), regardless of /compile setting.
3 - Write the textual target program, regardless of verification outcome
    and /compile setting.
Note, some compiler targets may (always or in some situations) write out the
textual target program as part of compilation, in which case /spillTargetCode:0
behaves the same way as /spillTargetCode:1.".TrimStart();
}
