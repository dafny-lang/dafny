namespace Microsoft.Dafny;

public class ReportFileOption : StringOption {
  public static readonly ReportFileOption Instance = new();
  public override object DefaultValue => null;
  public override string LongName => "report-file";
  public override string ArgumentName => "file";
  public override string Description =>
    "Specify a path to store the audit report file. " +
    "Without this, the report will take the form of standard warnings.";

  public override string PostProcess(DafnyOptions options) {
    options.AuditorReportFile = Get(options);
    return null;
  }
}