namespace Microsoft.Dafny;

public class CompareReportOption : BooleanOption {
  public static readonly CompareReportOption Instance = new();
  public override string LongName => "compare-report";

  public override string Description => @"
Compare the report that would have been generated with the
existing file given by --report-file, and fail if they differ.";

  public override string PostProcess(DafnyOptions options) {
    options.CompareAuditReport = true;
    return null;
  }
}
