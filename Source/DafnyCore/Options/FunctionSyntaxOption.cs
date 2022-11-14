using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class FunctionSyntaxOption : StringOption {
  public static readonly FunctionSyntaxOption Instance = new();
  public override object DefaultValue => "3";
  public override string LongName => "function-syntax";
  public override string ArgumentName => "version";

  public override string Description => @"
      The syntax for functions is changing from Dafny version 3 to version
      4. This switch gives early access to the new syntax, and also
      provides a mode to help with migration.
  
      3 (default) - Compiled functions are written `function method` and
          `predicate method`. Ghost functions are written `function` and
          `predicate`.
      4 - Compiled functions are written `function` and `predicate`. Ghost
          functions are written `ghost function` and `ghost predicate`.
      migration3to4 - Compiled functions are written `function method` and
          `predicate method`. Ghost functions are written `ghost function`
          and `ghost predicate`. To migrate from version 3 to version 4,
          use this flag on your version 3 program. This will give flag all
          occurrences of `function` and `predicate` as parsing errors.
          These are ghost functions, so change those into the new syntax
          `ghost function` and `ghost predicate`. Then, start using
          /functionSyntax:4. This will flag all occurrences of `function
          method` and `predicate method` as parsing errors. So, change
          those to just `function` and `predicate`. Now, your program uses
          version 4 syntax and has the exact same meaning as your previous
          version 3 program.
      experimentalDefaultGhost - Like migration3to4, but allow `function`
          and `predicate` as alternatives to declaring ghost functions and
          predicates, respectively.
      experimentalDefaultCompiled - Like migration3to4, but allow
          `function` and `predicate` as alternatives to declaring compiled
          functions and predicates, respectively.
      experimentalPredicateAlwaysGhost - Compiled functions are written
          `function`. Ghost functions are written `ghost function`.
          Predicates are always ghost and are written `predicate`.".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    var value = Get(options);
    if (value == "3") {
      options.FunctionSyntax = DafnyOptions.FunctionSyntaxOptions.Version3;
    } else if (value == "4") {
      options.FunctionSyntax = DafnyOptions.FunctionSyntaxOptions.Version4;
    } else if (value == "migration3to4") {
      options.FunctionSyntax = DafnyOptions.FunctionSyntaxOptions.Migration3To4;
    } else if (value == "experimentalDefaultGhost") {
      options.FunctionSyntax = DafnyOptions.FunctionSyntaxOptions.ExperimentalTreatUnspecifiedAsGhost;
    } else if (value == "experimentalDefaultCompiled") {
      options.FunctionSyntax = DafnyOptions.FunctionSyntaxOptions.ExperimentalTreatUnspecifiedAsCompiled;
    } else if (value == "experimentalPredicateAlwaysGhost") {
      options.FunctionSyntax = DafnyOptions.FunctionSyntaxOptions.ExperimentalPredicateAlwaysGhost;
    } else {
      return $"Invalid argument to option {LongName}";
    }

    return null;
  }
}