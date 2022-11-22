using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class FunctionSyntaxOption : StringOption {
  public static readonly FunctionSyntaxOption Instance = new();
  public override object DefaultValue => "3";
  public override string LongName => "function-syntax";
  public override string ArgumentName => "version";

  public override string Description => @"
The syntax for functions is changing from Dafny version 3 to version 4. This switch gives early access to the new syntax, and also provides a mode to help with migration.

3 (default) - Compiled functions are written `function method` and `predicate method`. Ghost functions are written `function` and `predicate`.
4 - Compiled functions are written `function` and `predicate`. Ghost functions are written `ghost function` and `ghost predicate`.
migration3to4 - Compiled functions are written `function method` and `predicate method`. Ghost functions are written `ghost function` and `ghost predicate`. To migrate from version 3 to version 4, use this flag on your version 3 program. This will give flag all occurrences of `function` and `predicate` as parsing errors. These are ghost functions, so change those into the new syntax `ghost function` and `ghost predicate`. Then, start using --functionSyntax:4. This will flag all occurrences of `function method` and `predicate method` as parsing errors. So, change those to just `function` and `predicate`. Now, your program uses version 4 syntax and has the exact same meaning as your previous version 3 program.
experimentalDefaultGhost - Like migration3to4, but allow `function` and `predicate` as alternatives to declaring ghost functions and predicates, respectively.
experimentalDefaultCompiled - Like migration3to4, but allow `function` and `predicate` as alternatives to declaring compiled
    functions and predicates, respectively.
experimentalPredicateAlwaysGhost - Compiled functions are written `function`. Ghost functions are written `ghost function`. Predicates are always ghost and are written `predicate`.".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    var value = Get(options);
    DafnyOptions.FunctionSyntaxOptions? syntax = value switch {
      "3" => DafnyOptions.FunctionSyntaxOptions.Version3,
      "4" => DafnyOptions.FunctionSyntaxOptions.Version4,
      "migration3to4" => DafnyOptions.FunctionSyntaxOptions.Migration3To4,
      "experimentalDefaultGhost" => DafnyOptions.FunctionSyntaxOptions.ExperimentalTreatUnspecifiedAsGhost,
      "experimentalDefaultCompiled" => DafnyOptions.FunctionSyntaxOptions.ExperimentalTreatUnspecifiedAsCompiled,
      "experimentalPredicateAlwaysGhost" => DafnyOptions.FunctionSyntaxOptions.ExperimentalPredicateAlwaysGhost,
      _ => null
    };

    if (syntax == null) {
      return $"Invalid argument to option {LongName}";
    }

    options.FunctionSyntax = syntax.Value;
    return null;
  }
}
