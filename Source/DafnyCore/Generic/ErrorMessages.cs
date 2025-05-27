using System.Collections.Generic;

namespace Microsoft.Dafny;

static class ErrorMessages {
  public static string GetMessage(string errorId, params object[] arguments) {
    var formatMsg = Messages.GetValueOrDefault(errorId);
    if (formatMsg == null) {
      return (string)(arguments[0]);
    }

    return string.Format(formatMsg, arguments);
  }

  public static Dictionary<string, string> Messages = new() {
    {
      "ConstraintIsNotCompilable",
      "{0} is a {1} and its constraint is not compilable, hence it cannot yet be used as the type of a bound variable in {2}."
    },
    { "ConstraintIsNotCompilableBecause", "The constraint is not compilable because {0}" },
    { "LibraryImpliesLocalOption", "{0}: --{1} is set locally to {2}, but the library was built with {3}" }, {
      "r_assert_only_assumes_others", "Assertion with {:only} temporarily transforms other assertions into assumptions"
    },
    { "r_assert_only_before_after", "{:only} only accepts \"before\" or \"after\" as an optional argument" },
    { "RedundantBranch", "this branch is redundant" }, {
      "UnverifiedLibrary",
      "The file '{0}' was passed to --library. Verification for that file might have used options incompatible with the current ones, or might have been skipped entirely. Use a .doo file to enable Dafny to check that compatible options were used"
    },
    { "ConstructorWrongArity", "constructor {0} of arity {2} is applied to {1} argument(s)" },
    { "MemberDoesNotExist", "member {0} does not exist in type {1}" },
    { "p_internal_exception", "[internal error] Parser exception: {0}\n{1}" },
    { "c_assign_such_that_forbidden", "assign-such-that statement forbidden by the --enforce-determinism option" },
    { "r_no_assign_to_var_in_ghost", "cannot assign to {0} in a ghost context" },
    { "r_no_assign_ghost_to_var", "{0} cannot be assigned a value that depends on a ghost" },
  };
}