using System.CommandLine;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class StrictDefiniteAssignmentOption : BooleanOption {
  public static readonly StrictDefiniteAssignmentOption Instance = new();

  public override string LongName => "strict-definite-assignment";

  public override string Description => @"
Additionally enforce definite-assignment rules for 
variables that are ghost or whose types support auto-initialisation,
so it is enforced for all non-yield-parameter variables and fields.";

  public override string PostProcess(DafnyOptions options) {
    options.DefiniteAssignmentLevel = Get(options) ? 2 : 1;
    return null;
  }
}
