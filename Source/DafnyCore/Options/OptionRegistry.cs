using System;
using System.Collections.Generic;
using System.CommandLine;
using System.Linq;
using Microsoft.Dafny;

namespace Microsoft.Dafny;

public class OptionRegistry {

  /// <summary>
  /// Check that the .doo file format is aware of all options,
  /// and therefore which have to be saved to safely support separate verification/compilation.
  /// </summary>
  public static void CheckOptionsAreKnown(IEnumerable<Option> allOptions) {
    var unsupportedOptions = allOptions.ToHashSet()
      .Where(o =>
        !optionScopes.ContainsKey(o))
      .ToList();
    if (unsupportedOptions.Any()) {
      throw new Exception($"Internal error - unsupported options registered: {{\n{string.Join(",\n", unsupportedOptions)}\n}}");
    }
  }

  // Partitioning of all options into subsets that must be recorded in a .doo file
  // to guard against unsafe usage.
  // Note that legacy CLI options are not as cleanly enumerated and therefore
  // more difficult to completely categorize, which is the main reason the LibraryBackend
  // is restricted to only the new CLI.
  private static readonly Dictionary<Option, GlobalOptionCheck> globalOptionChecks = new();
  private static readonly Dictionary<Option, OptionScope> optionScopes = new();

  public static IEnumerable<Option> GlobalOptions => globalOptionChecks.Keys;
  public static IEnumerable<Option> TranslationOptions => optionScopes.Where(kv => kv.Value == OptionScope.Translation).Select(kv => kv.Key);
  public static IEnumerable<(Option option, GlobalOptionCheck check)> GlobalChecks =>
    globalOptionChecks.Select(kv => (kv.Key, kv.Value));

  public static void RegisterOption(Option option, OptionScope scope) {
    if (scope == OptionScope.Global) {
      throw new ArgumentException("Please call RegisterGlobalOption instead");
    }

    optionScopes[option] = scope;
  }
  public static void RegisterGlobalOption(Option option, GlobalOptionCheck check) {
    optionScopes[option] = OptionScope.Global;
    globalOptionChecks[option] = check;
  }

  // public static void RegisterLibraryCheck(Option option, OptionCompatibility.OptionCheck check) {
  //   if (NoChecksNeeded.Contains(option)) {
  //     throw new ArgumentException($"Option already registered as not needing a library check: {option.Name}");
  //   }
  //   OptionChecks.Add(option, check);
  // }
  //
  // public static void RegisterLibraryChecks(IDictionary<Option, OptionCompatibility.OptionCheck> checks) {
  //   foreach (var (option, check) in checks) {
  //     RegisterLibraryCheck(option, check);
  //   }
  // }
  //
  // public static void RegisterNoChecksNeeded(Option option, bool semantic) {
  //   if (semantic) {
  //     RegisterLibraryCheck(option, OptionCompatibility.NoOpOptionCheck);
  //   } else {
  //     if (OptionChecks.ContainsKey(option)) {
  //       throw new ArgumentException($"Option already registered as needing a library check: {option.Name}");
  //     }
  //     NoChecksNeeded.Add(option);
  //   }
  // }
}

public enum OptionScope { Cli, Global, Module, Translation }

public delegate bool GlobalOptionCheck(ErrorReporter reporter, IToken origin, string prefix, Option option, object localValue, object libraryValue);