using System.Collections.Generic;
using System.CommandLine;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public static class BoogieOptionBag {
  public static readonly Option<IEnumerable<string>> BoogieFilter = new("--boogie-filter", @"
(experimental) Only check proofs whose Boogie name is matched by pattern <p>. This option may be specified multiple times to match multiple patterns. The pattern <p> may contain * wildcards which match any character zero or more times. If you are unsure of how Boogie names are generated, please pre- and postfix your pattern with a wildcard to enable matching on Dafny proof names."
    .TrimStart()) {
    ArgumentHelpName = "pattern"
  };

  public static readonly Option<string> BoogieArguments = new("--boogie",
    "Specify arguments that are passed to Boogie, a tool used to verify Dafny programs.") {
    ArgumentHelpName = "arguments",
  };

  public static readonly Option<uint> Cores = new("--cores", () => 0,
    "Run the Dafny CLI using <n> cores. Specifying 0 will use half of the available processor cores.") {
    ArgumentHelpName = "count"
  };

  public static readonly Option<bool> NoVerify = new("--no-verify",
    "Skip verification") {
    ArgumentHelpName = "count"
  };

  public static readonly Option<uint> VerificationTimeLimit = new("--verification-time-limit",
    "Limit the number of seconds spent trying to verify each procedure") {
    ArgumentHelpName = "seconds"
  };

  static BoogieOptionBag() {
    DafnyOptions.RegisterLegacyBinding(BoogieFilter, (o, f) => o.ProcsToCheck.AddRange(f));
    DafnyOptions.RegisterLegacyBinding(BoogieArguments, (o, boogieOptions) => {

      if (boogieOptions != null) {
        o.Parse(SplitArguments(boogieOptions).ToArray());
      }
    });
    DafnyOptions.RegisterLegacyBinding(Cores,
      (o, f) => o.VcsCores = f == 0 ? (1 + System.Environment.ProcessorCount) / 2 : (int)f);
    DafnyOptions.RegisterLegacyBinding(NoVerify, (o, f) => o.Verify = !f);
    DafnyOptions.RegisterLegacyBinding(VerificationTimeLimit, (o, f) => o.TimeLimit = f);
  }

  private static IReadOnlyList<string> SplitArguments(string commandLine) {
    var inSingleQuote = false;
    var inDoubleQuote = false;
    var result = new List<string>();
    var start = 0;
    for (var end = 0; end < commandLine.Length; end++) {
      var store = false;
      if (commandLine[end] == '"' && !inSingleQuote) {
        store = inDoubleQuote;
        inDoubleQuote = !inDoubleQuote;
      }
      if (commandLine[end] == '\'' && !inDoubleQuote) {
        store = inSingleQuote;
        inSingleQuote = !inSingleQuote;
      }
      if (!inSingleQuote && !inDoubleQuote && commandLine[end] == ' ') {
        store = true;
      }

      if (store) {
        result.Add(commandLine.Substring(start, end - start));
        start = end + 1; // Skip the single or double quote or space in the next entry
      }
    }
    result.Add(commandLine.Substring(start, commandLine.Length - start));
    return result;
  }
}
