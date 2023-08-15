using System;
using System.Linq;

namespace Microsoft.Dafny;

public enum CoverageLabel {
  FullyCovered,
  NotCovered,
  PartiallyCovered
}

public static class CoverageLabelExtension {

  /// <summary>
  /// Combine coverage labels. E.g. FullyCovered + NotCovered = PartiallyCovered
  /// </summary>
  public static CoverageLabel Combine(CoverageLabel one, CoverageLabel two) {
    if (one == CoverageLabel.PartiallyCovered || two == CoverageLabel.PartiallyCovered || one != two) {
      return CoverageLabel.PartiallyCovered;
    }
    return one;
  }

  public static string ToString(CoverageLabel label) {
    return label switch {
      CoverageLabel.FullyCovered => "fully covered",
      CoverageLabel.NotCovered => "not covered",
      CoverageLabel.PartiallyCovered => "partially covered",
      _ => ""
    };
  }

  /// <summary>
  /// Return HTML class used to highlight lines in different colors depending on the coverage.
  /// Look at assets/.resources/coverage.css for the styles corresponding to these classes
  /// </summary>
  public static string ToHtmlClass(CoverageLabel label) {
    return label switch {
      CoverageLabel.FullyCovered => "fc",
      CoverageLabel.NotCovered => "nc",
      CoverageLabel.PartiallyCovered => "pc",
      _ => ""
    };
  }

  /// <summary> Inverse of ToHtmlClass </summary>
  public static CoverageLabel FromHtmlClass(string htmlClass) {
    foreach (var label in Enum.GetValues(typeof(CoverageLabel)).Cast<CoverageLabel>()) {
      if (ToHtmlClass(label) == htmlClass) {
        return label;
      }
    }
    return CoverageLabel.NotCovered; // this is a fallback in case the HTML has invalid classes
  }

}