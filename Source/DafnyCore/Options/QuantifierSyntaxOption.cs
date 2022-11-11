namespace Microsoft.Dafny;

class QuantifierSyntaxOption : StringOption {
  public static readonly QuantifierSyntaxOption Instance = new();
  public override object DefaultValue => "3";
  public override string LongName => "quantifier-syntax";
  public override string ArgumentName => "version";

  public override string Description => @"
      The syntax for quantification domains is changing from Dafny version
      3 to version 4, more specifically where quantifier ranges (|
      <Range>) are allowed. This switch gives early access to the new
      syntax.
  
      3 (default) - Ranges are only allowed after all quantified variables
          are declared. (e.g. set x, y | 0 <= x < |s| && y in s[x] && 0 <=
          y :: y)
      4 - Ranges are allowed after each quantified variable declaration.
          (e.g. set x | 0 <= x < |s|, y <- s[x] | 0 <= y :: y)
  
      Note that quantifier variable domains (<- <Domain>) are available in
      both syntax versions.".TrimStart();
  
  public override string PostProcess(DafnyOptions options) {
    var value = Get(options);
    if (value == "3") {
      options.QuantifierSyntax = DafnyOptions.QuantifierSyntaxOptions.Version3;
    } else if (value == "4") {
      options.QuantifierSyntax = DafnyOptions.QuantifierSyntaxOptions.Version4;
    } else {
      return $"Invalid argument to option {LongName}";
    }

    return null;
  }
}