using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny; 

public class FilterOption : CommandLineOption<IEnumerable<string>> {
  public static readonly FilterOption Instance = new();
  
  public override object DefaultValue => Enumerable.Empty<string>();
  public override string LongName => "filter";
  public override string ArgumentName => "pattern";

  public override string Description => @"
(experimental) Only check proofs matched by pattern <p>. This option
may be specified multiple times to match multiple patterns.
The pattern <p> matches the whole proof name and may
contain * wildcards which match any character zero or more
times.".TrimStart();
  public override void Parse(CommandLineParseState ps, DafnyOptions options) {
    throw new System.NotImplementedException();
  }

  public override string PostProcess(DafnyOptions options) {
    options.ProcsToCheck.AddRange(Get(options).Select(s => "*" + s + "*"));
    return null;
  }
}