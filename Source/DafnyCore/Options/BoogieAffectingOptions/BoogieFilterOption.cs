using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny; 

public class BoogieFilterOption : CommandLineOption<IEnumerable<string>> {
  public static readonly BoogieFilterOption Instance = new();

  public override object DefaultValue => Enumerable.Empty<string>();
  public override string LongName => "boogie-filter";
  public override string ArgumentName => "pattern";

  public override string Description => @"
(experimental) Only check proofs whose Boogie name is matched by pattern <p>. This option may be specified multiple times to match multiple patterns. The pattern <p> may contain * wildcards which match any character zero or more times. If you are unsure of how Boogie names are generated, please pre- and postfix your pattern with a wildcard to enable matching on Dafny proof names.".TrimStart();
  public override void Parse(CommandLineParseState ps, DafnyOptions options) {
    throw new System.NotImplementedException();
  }

  public override string PostProcess(DafnyOptions options) {
    options.ProcsToCheck.AddRange(Get(options));
    return null;
  }
}
