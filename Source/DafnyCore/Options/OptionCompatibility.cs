using System;
using System.Collections.Generic;
using System.CommandLine;
using Microsoft.Dafny;
using System.Linq;

namespace DafnyCore.Options;

public class OptionCompatibility {

  public static bool CheckOptionMatches(ErrorReporter reporter, IOrigin origin, string prefix, Option option, object localValue, object libraryValue) {
    if (OptionValuesEqual(option, localValue, libraryValue)) {
      return true;
    }

    reporter.Error(MessageSource.Project, origin,
      $"{prefix}: --{option.Name} is set locally to {OptionValueToString(option, localValue)}, " +
      $"but the library was built with {OptionValueToString(option, libraryValue)}");
    return false;
  }

  private static string OptionValueToString(Option option, object value) {
    if (option.ValueType == typeof(IEnumerable<string>)) {
      var values = (IEnumerable<string>)value;
      return $"[{string.Join(',', values)}]";
    }

    if (value == null) {
      return "a version of Dafny that does not have this option";
    }
    return value.ToString();
  }

  private static bool OptionValuesEqual(Option option, object first, object second) {
    if (first.Equals(second)) {
      return true;
    }

    if (option.ValueType == typeof(IEnumerable<string>)) {
      return ((IEnumerable<string>)first).SequenceEqual((IEnumerable<string>)second);
    }

    return false;
  }

  public static bool OptionValuesImplied(object first, object second) {
    try {
      return !(bool)first || (bool)second;
    } catch (NullReferenceException) {
      throw new Exception("Comparing options of Doo files created by different Dafny builds. You are probably using a locally built Dafny that has the same version as a different built.");
    }
  }

  public static bool OptionLibraryImpliesLocalError(ErrorReporter reporter, IOrigin origin, string prefix, Option option, object localValue, object libraryValue) {
    return CheckOptionLibraryImpliesLocal(reporter, origin, prefix, option, ErrorLevel.Error,
      localValue, libraryValue);
  }

  public static bool OptionLibraryImpliesLocalWarning(ErrorReporter reporter, IOrigin origin, string prefix, Option option, object localValue, object libraryValue) {
    return CheckOptionLibraryImpliesLocal(reporter, origin, prefix, option, ErrorLevel.Warning,
      localValue, libraryValue);
  }

  /// Checks that the library option ==> the local option.
  /// E.g. --no-verify: the only incompatibility is if it's on in the library but not locally.
  /// Generally the right check for options that weaken guarantees.
  private static bool CheckOptionLibraryImpliesLocal(ErrorReporter reporter, IOrigin origin, string prefix, Option option, ErrorLevel severity, object localValue, object libraryValue) {
    if (OptionValuesImplied(libraryValue, localValue)) {
      return true;
    }

    reporter.Message(MessageSource.Project, severity, "", origin,
      $"{prefix}: --{option.Name} is set locally to {OptionValueToString(option, localValue)}, but the library was built with {OptionValueToString(option, libraryValue)}");
    return false;
  }

  /// Checks that the local option ==> the library option.
  /// E.g. --track-print-effects: the only incompatibility is if it's on locally but not in the library.
  /// Generally the right check for options that strengthen guarantees.
  public static bool CheckOptionLocalImpliesLibrary(ErrorReporter reporter, IOrigin origin, string prefix, Option option, object localValue, object libraryValue) {
    if (OptionValuesImplied(localValue, libraryValue)) {
      return true;
    }
    reporter.Error(MessageSource.Project, origin, LocalImpliesLibraryMessage(prefix, option, localValue, libraryValue));
    return false;
  }

  public static string LocalImpliesLibraryMessage(string prefix, Option option, object localValue, object libraryValue) {
    return $"{prefix}: --{option.Name} is set locally to {OptionValueToString(option, localValue)}, but the library was built with {OptionValueToString(option, libraryValue)}";
  }


  // Placeholder no-op check, used for options that need to be recorded but don't require any compatibility check.
  public static bool NoOpOptionCheck(ErrorReporter reporter, IOrigin origin, string prefix, Option option, object localValue, object libraryValue) {
    return true;
  }
}